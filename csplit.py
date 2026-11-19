#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
csplit.py v2.6.6 — 通用 C 源码自动拆分 / 混淆工具（修复版）

修复 (v2.6.6):
  - junk 注入不再硬编码 ['main','warmup',...]，自动兜底任意 func_def
  - n_checks==0 的 decoy 文件加 constructor 强引用，防 -flto 死代码删除
  - ds_get 清零改用 volatile 防止编译器优化掉
  - 清理 process_file_signatures / _fscheck_block 的重复定义
  - 删除已无调用方的 inject_junk_checks 单文件版
  - 新增 --strict-parse / --dry-run

历史 (v2.6.0):
  - 6 层 Feistel 字符串加密
  - 全局 const char *x[] 数组加密 + constructor 注入
  - ds_get / j_* / _adbg_* 等内部名随 --obfuscate-symbols 混淆
  - 字符串 ID 随机打散（ds_idx_pos 排列表）
  - anti-debug 多检测：TracerPid + /proc/self/maps + LD_PRELOAD
"""
import os, sys, re, json, argparse, subprocess, random, string
from collections import defaultdict

# ================= 数据结构 =================
class Item:
    __slots__ = ('kind','text','core','name','is_static',
                 'signature','body','refs','group','export')
    def __init__(self, kind, text, core=None):
        self.kind = kind
        self.text = text
        self.core = core if core is not None else text
        self.name = None
        self.is_static = False
        self.signature = None
        self.body = None
        self.refs = set()
        self.group = None
        self.export = False

# ================= 关键字 =================
KEYWORDS = set("""auto break case char const continue default do double else enum
extern float for goto if inline int long register restrict return short signed
sizeof static struct switch typedef union unsigned void volatile while _Bool
_Complex _Imaginary NULL true false size_t ssize_t""".split())

def _read_source_file(path):
    """尝试 utf-8 → utf-8-sig → gbk → latin-1，全失败则退出。"""
    for enc in ('utf-8', 'utf-8-sig', 'gbk', 'latin-1'):
        try:
            with open(path, 'r', encoding=enc) as f:
                return f.read()
        except (UnicodeDecodeError, LookupError):
            continue
        except OSError as e:
            print(f'[错误] 读取 {path} 失败: {e}', file=sys.stderr)
            sys.exit(1)
    print(f'[错误] 无法解码 {path}（尝试 utf-8/utf-8-sig/gbk/latin-1 均失败）',
          file=sys.stderr)
    sys.exit(1)

# ================= 字符串字面量扫描 =================
def _find_string_positions(text):
    results = []
    n = len(text); i = 0
    bracket_stack = []
    prev_tok = ''
    # 额外追踪：最近一次 '=' 之前最后 1~3 个 token，用于判断是否数组声明
    prev_tokens = []
    while i < n:
        c = text[i]
        if c == '/' and i + 1 < n:
            if text[i + 1] == '/':
                e = text.find('\n', i); i = n if e < 0 else e + 1; continue
            if text[i + 1] == '*':
                e = text.find('*/', i + 2); i = n if e < 0 else e + 2; continue
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '\\': j += 2; continue
                if text[j] == '"':  j += 1; break
                j += 1
            in_brace = bool(bracket_stack) and bracket_stack[-1] == '{'

            # === 新的 is_init 判定 ===
            # 只有以下情况才算"必须编译期常量"：
            #   (a) 函数体内 `{ "x", "y" }` 数组字面量：prev_tok == '{' 或 ','
            #   (b) `T[] = "abc"` 类型数组声明：prev_tok == '=' 且 prev_tokens 末尾有 ']'
            is_init = False
            if in_brace and prev_tok in ('{', ','):
                is_init = True
            elif prev_tok == '=':
                # 看 '=' 之前的 token 序列：是否形如 `char x[N] =` / `T[] =`
                # 取 prev_tokens 最后 1~3 个
                tail = prev_tokens[-3:] if len(prev_tokens) >= 1 else []
                # 有 ']' 说明是数组声明
                if ']' in tail:
                    is_init = True

            results.append((i, j, text[i + 1:j - 1], is_init))
            prev_tok = '"'
            prev_tokens.append('"')
            i = j; continue

        if c == '\'':
            j = i + 1
            while j < n:
                if text[j] == '\\': j += 2; continue
                if text[j] == '\'': j += 1; break
                j += 1
            prev_tok = '\''
            prev_tokens.append('\'')
            if len(prev_tokens) > 8: prev_tokens = prev_tokens[-8:]
            i = j; continue

        if c in '([{':
            bracket_stack.append(c); prev_tok = c
            prev_tokens.append(c)
        elif c in ')]}':
            if bracket_stack: bracket_stack.pop()
            prev_tok = c
            prev_tokens.append(c)
        elif c.isalnum() or c == '_':
            # 标识符：作为一个 token 收集
            k = i
            while k < n and (text[k].isalnum() or text[k] == '_'): k += 1
            prev_tokens.append(text[i:k])
            prev_tok = text[i]  # 用一个非空白字符示意
            i = k; continue
        elif c not in ' \t\r\n':
            prev_tok = c
            prev_tokens.append(c)

        if len(prev_tokens) > 8: prev_tokens = prev_tokens[-8:]
        i += 1
    return results

# ================= Junk 校验 =================
MASK64 = 0xFFFFFFFFFFFFFFFF
JK_MUL = 0x9E3779B97F4A7C15

def _jk_a(x):
    x &= MASK64; x ^= x >> 33
    x = (x * 0xff51afd7ed558ccd) & MASK64
    x ^= x >> 33; return x & MASK64

def _jk_b(x, table):
    x &= MASK64; r = 0
    for i in range(8):
        b = table[(x >> (i * 8)) & 0xF]
        r = ((r << 8) | b) & MASK64
    return r

def _jk_c(x):
    x &= MASK64
    for _ in range(5):
        t = ((x << 3) ^ (x >> 2)) & MASK64
        x = (x + t) & MASK64
    return x

def _jk_compute(n, seed, table):
    x = (seed + (n * JK_MUL)) & MASK64
    x = _jk_a(x); x = _jk_b(x, table); x = _jk_c(x); return x

def gen_junk_h(outdir, fname, ck_name, panic_name, sym_map=None, basename='junk'):
    guard = 'CSPLIT_' + re.sub(r'\W', '_', basename).upper() + '_H'
    L = ['/* auto-generated */',
         f'#ifndef {guard}', f'#define {guard}', '',
         f'int  {ck_name}(int n);',
         f'void {panic_name}(void) __attribute__((noreturn));', '',
         '#endif', '']
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map or {})

def gen_junk_c(outdir, fname, n_checks, seed, table, expected,
               panic_code, ck_name, panic_name, sym_map=None, ctor_base=200):
    if n_checks == 0:
        L = [
            '/* auto-generated — junk decoy (0 checks, LTO-safe) */',
            '#include <stdint.h>',
            '#include <stdlib.h>',
            '#include <unistd.h>',
            '',
            '__attribute__((noinline, used))',
            f'int {ck_name}(int n) {{ (void)n; return 0; }}',
            '',
            '__attribute__((noreturn, noinline, used))',
            f'void {panic_name}(void) {{ _Exit({panic_code}); }}',
            '',
            '/* 强制引用 ck，防 -flto 当死代码删除 */',
            f'__attribute__((constructor({ctor_base + 2}), used))',   # 改动
            f'static void _zkeep_{ck_name}(void) {{',
            f'    volatile int r = {ck_name}(0);',
            '    (void)r;',
            '}',
            ''
        ]
        _write(outdir, fname, '\n'.join(L) + '\n', sym_map or {})
        return
    # —— 以下保持 v2.6.6 原样 ——
    def fmt_u64(xs):
        lines = []
        for i in range(0, len(xs), 4):
            chunk = xs[i:i+4]
            lines.append('    ' + ', '.join(f'0x{x:016x}ULL' for x in chunk) + ',')
        return '\n'.join(lines)
    tbl_str = ', '.join(f'0x{b:02x}' for b in table)

    dbg_name = [b ^ 0x3B for b in b'CSPLIT_ADBG_DEBUG']
    fmt_str  = [b ^ 0x7D for b in b'[junk] ck_%d FAIL: got=0x%016llx exp=0x%016llx\n']

    def arr(name, bs):
        return (f'static const unsigned char {name}[{len(bs)}] = {{'
                + ', '.join(f'0x{b:02x}' for b in bs) + '};')

    L = [
        '/* auto-generated — junk v2.6.8 */',
        '#include <stdint.h>',
        '#include <stdlib.h>',
        '#include <stdio.h>',
        '#include <unistd.h>',
        '',
        arr('_j_dbg_name', dbg_name),
        arr('_j_fmt',      fmt_str),
        '',
        'static char _j_buf_name[32];',
        'static char _j_buf_fmt[64];',
        'static int  _j_inited = 0;',
        'static int  _j_debug  = 0;',
        '',
        '__attribute__((noinline))',
        'static void _j_prepare(void) {',
        '    if (_j_inited) return;',
        '    volatile unsigned char t;',
        '    for (int i = 0; i < (int)sizeof(_j_dbg_name); i++) {',
        '        t = _j_dbg_name[i]; _j_buf_name[i] = (char)(t ^ 0x3B);',
        '    }',
        '    _j_buf_name[sizeof(_j_dbg_name)] = 0;',
        '    for (int i = 0; i < (int)sizeof(_j_fmt); i++) {',
        '        t = _j_fmt[i]; _j_buf_fmt[i] = (char)(t ^ 0x7D);',
        '    }',
        '    _j_buf_fmt[sizeof(_j_fmt)] = 0;',
        '    const char *v = getenv(_j_buf_name);',
        '    _j_debug = (v && v[0] == \'1\') ? 1 : 0;',
        '    _j_inited = 1;',
        '}',
        '',
        '__attribute__((noinline, used))',
        'static uint64_t j_a(uint64_t x) {',
        '    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; return x; }', '',
        '__attribute__((noinline, used))',
        'static uint64_t j_b(uint64_t x) {',
        f'    static const unsigned char T[16] = {{ {tbl_str} }};',
        '    uint64_t r = 0;',
        '    for (int i = 0; i < 8; i++) r = (r << 8) | T[(x >> (i * 8)) & 0xF];',
        '    return r; }', '',
        '__attribute__((noinline, used))',
        'static uint64_t j_c(uint64_t x) {',
        '    for (int i = 0; i < 5; i++) { uint64_t t = (x << 3) ^ (x >> 2); x += t; }',
        '    return x; }', '',
        '__attribute__((noinline, used))',
        'static uint64_t j_compute(int n) {',
        f'    static const uint64_t SEED_CONST = 0x{seed:016x}ULL;',
        '    volatile uint64_t s = SEED_CONST;',
        f'    uint64_t x = s + (uint64_t)n * 0x{JK_MUL:016x}ULL;',
        '    x = j_a(x); x = j_b(x); x = j_c(x); return x; }', '',
        f'static const uint64_t _ck_expected[{n_checks}] = {{',
        fmt_u64(expected), '};', '',
        '__attribute__((noinline, used))',
        f'int {ck_name}(int n) {{',
        f'    if (n < 0 || n >= {n_checks}) return 0;',
        '    volatile uint64_t got = j_compute(n);',
        '    volatile uint64_t exp = _ck_expected[n];',
        '    if (got != exp) {',
        '        _j_prepare();',
        '        if (_j_debug)',
        '            fprintf(stderr, _j_buf_fmt, n,',
        '                    (unsigned long long)got, (unsigned long long)exp);',
        '        return 0;',
        '    }',
        '    return 1; }', '',
        '__attribute__((noreturn, noinline, used))',
        f'void {panic_name}(void) {{',
        '    volatile uint64_t x = 0;',
        '    for (int i = 0; i < 64; i++) x += i * 17;',
        f'    (void)x; _Exit({panic_code}); }}', ''
    ]
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map or {})

def _find_body_inject_pos(text, brace_idx):
    i = brace_idx + 1; n = len(text)
    while i < n:
        while i < n and text[i] in ' \t\r\n': i += 1
        if i + 1 < n and text[i] == '/' and text[i+1] == '/':
            e = text.find('\n', i); i = n if e < 0 else e + 1; continue
        if i + 1 < n and text[i] == '/' and text[i+1] == '*':
            e = text.find('*/', i + 2); i = n if e < 0 else e + 2; continue
        break
    return i

def inject_junk_checks_multi(items, targets, junk_modules):
    """多文件版：targets: {函数名: [(mod_idx, local_check_idx), ...]}"""
    for it in items:
        if it.kind != 'func_def' or it.name not in targets:
            continue
        b = find_body_brace(it.text)
        if b < 0:
            continue
        pos = _find_body_inject_pos(it.text, b)
        stmts = ''.join(
            f'    if (!{junk_modules[mi]["ck"]}({li})) '
            f'{junk_modules[mi]["panic"]}();\n'
            for (mi, li) in targets[it.name])
        it.text = it.text[:pos] + stmts + it.text[pos:]

def _pick_junk_inject_targets(items, pool_priority):
    """按优先级选 junk 注入目标，兜底选任意 func_def。
    返回候选函数名列表（已去重、按优先级排序）。
    若源码一个 func_def 都没有，返回 []。"""
    all_funcs = [it.name for it in items if it.kind == 'func_def' and it.name]
    if not all_funcs:
        return []
    result = []
    for fn in pool_priority:
        if fn in all_funcs and fn not in result:
            result.append(fn)
    # 兜底 1：任意非 static 函数
    for it in items:
        if it.kind == 'func_def' and it.name and it.name not in result and not it.is_static:
            result.append(it.name)
    # 兜底 2：任意 static 函数
    for it in items:
        if it.kind == 'func_def' and it.name and it.name not in result:
            result.append(it.name)
    return result

def inject_junk_checks_safe(items, n_checks, junk_modules, pool_priority):
    """v2.6.6 — 健壮版 junk 注入：
      - 自动选目标函数（不硬编码）
      - 无可用目标函数时返回空 dict（不崩、不静默坏）
      - check 数超过函数数时轮流分摊
      - 返回实际注入的 {fn_name: [(mi, li), ...]}"""
    if not junk_modules or n_checks <= 0:
        return {}
    targets_available = _pick_junk_inject_targets(items, pool_priority)
    if not targets_available:
        return {}
    check_plan = [(mi, li) for mi, jm in enumerate(junk_modules)
                  for li in range(jm['n'])]
    if not check_plan:
        return {}
    targets = {}
    for ci, plan in enumerate(check_plan):
        fn = targets_available[ci % len(targets_available)]
        targets.setdefault(fn, []).append(plan)
    inject_junk_checks_multi(items, targets, junk_modules)
    return targets

# ================= 加密工具 =================
def _ror3(x): return ((x >> 3) | (x << 5)) & 0xFF
def _gen_krot(rng): return bytes(rng.randint(0, 255) for _ in range(16))

def _find_str_end(text, i):
    n = len(text); j = i + 1
    while j < n:
        if text[j] == '\\': j += 2; continue
        if text[j] == '"': return j + 1
        j += 1
    return -1

def merge_adjacent_strings(text):
    out = []; i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '/' and i+1 < n:
            if text[i+1] == '/':
                e = text.find('\n', i)
                if e < 0: out.append(text[i:]); break
                out.append(text[i:e+1]); i = e+1; continue
            if text[i+1] == '*':
                e = text.find('*/', i+2)
                if e < 0: out.append(text[i:]); break
                out.append(text[i:e+2]); i = e+2; continue
        if c == '"':
            end = _find_str_end(text, i)
            if end < 0: out.append(text[i:]); break
            content = text[i+1:end-1]; cur_end = end
            while True:
                k = cur_end
                while k < n and text[k] in ' \t\r\n': k += 1
                if k < n and text[k] == '"':
                    e2 = _find_str_end(text, k)
                    if e2 < 0: break
                    content += text[k+1:e2-1]; cur_end = e2
                else: break
            out.append('"' + content + '"'); i = cur_end
        elif c == '\'':
            j = i + 1
            while j < n:
                if text[j] == '\\': j += 2; continue
                if text[j] == '\'': j += 1; break
                j += 1
            out.append(text[i:j]); i = j
        else:
            out.append(c); i += 1
    return ''.join(out)

def is_adjacent_concat(text, start, end):
    n = len(text)
    j = start - 1
    while j >= 0 and text[j] in ' \t\r\n': j -= 1
    if j >= 0:
        c = text[j]
        if c == '"': return True
        if c.isalnum() or c == '_':
            k = j
            while k >= 0 and (text[k].isalnum() or text[k] == '_'): k -= 1
            tok = text[k+1:j+1]
            if tok and tok not in KEYWORDS: return True
    j = end
    while j < n and text[j] in ' \t\r\n': j += 1
    if j < n:
        c = text[j]
        if c == '"': return True
        if c.isalpha() or c == '_':
            k = j
            while k < n and (text[k].isalnum() or text[k] == '_'): k += 1
            tok = text[j:k]
            if tok and tok not in KEYWORDS: return True
    return False

def extract_string_literals(text):
    results = []; i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '/' and i+1 < n:
            if text[i+1] == '/':
                e = text.find('\n', i); i = n if e < 0 else e+1; continue
            if text[i+1] == '*':
                e = text.find('*/', i+2); i = n if e < 0 else e+2; continue
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '\\': j += 2; continue
                if text[j] == '"': j += 1; break
                j += 1
            results.append((i, j, text[i+1:j-1])); i = j
        elif c == '\'':
            j = i + 1
            while j < n:
                if text[j] == '\\': j += 2; continue
                if text[j] == '\'': j += 1; break
                j += 1
            i = j
        else:
            i += 1
    return results

def unescape_c_string(s):
    out = bytearray(); i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c == '\\' and i+1 < n:
            nc = s[i+1]; i += 2
            if   nc == 'n': out.append(10)
            elif nc == 't': out.append(9)
            elif nc == 'r': out.append(13)
            elif nc == 'a': out.append(7)
            elif nc == 'b': out.append(8)
            elif nc == 'f': out.append(12)
            elif nc == 'v': out.append(11)
            elif nc == '\\': out.append(92)
            elif nc == '"': out.append(34)
            elif nc == '\'': out.append(39)
            elif nc == '?': out.append(63)
            elif nc == 'x':
                hx = ''
                while i < n and len(hx) < 2 and s[i] in '0123456789abcdefABCDEF':
                    hx += s[i]; i += 1
                out.append(int(hx, 16) if hx else 0)
            elif nc in '01234567':
                oct_str = nc
                while i < n and len(oct_str) < 3 and s[i] in '01234567':
                    oct_str += s[i]; i += 1
                out.append(int(oct_str, 8) & 0xFF)
            else:
                out.append(ord(nc) & 0xFF)
        else:
            out.extend(c.encode('utf-8')); i += 1
    return bytes(out)

def _encrypt_one(content, rng, krot):
    """6 层 Feistel 风格，与 ds_get 严格互逆。"""
    raw = unescape_c_string(content)
    key = rng.randint(1, 255)
    s   = rng.randint(0, 255)
    enc = bytearray()
    for i, p in enumerate(raw):
        v1 = p ^ key
        v2 = ((v1 << 3) | (v1 >> 5)) & 0xFF
        k1 = (krot[(i + s) & 0xF] ^ (i * 37)) & 0xFF
        v3 = (v2 + k1) & 0xFF
        k2 = (krot[(i * 3 + s + 7) & 0xF] ^ ((i * 91 + 13) & 0xFF)) & 0xFF
        v4 = v3 ^ k2
        v5 = ((v4 >> 5) | (v4 << 3)) & 0xFF
        c  = (v5 + key) & 0xFF
        enc.append(c)
    return (bytes(enc), key, s)

def dump_keys(outdir, krot, unique_strings, encrypted_data, seed):
    path = os.path.join(outdir, 'keys.txt')
    with open(path, 'w') as f:
        f.write('# csplit.py v2.6.6 key dump\n')
        f.write(f'SEED  = {seed}\n')
        f.write(f'KROT  = {",".join(f"0x{b:02x}" for b in krot)}\n#\n')
        f.write('# ID      KEY     SEED    明文预览\n')
        for content, idx in sorted(unique_strings.items(), key=lambda kv: kv[1]):
            enc, key, s = encrypted_data[idx]
            preview = (content.replace('\\', '\\\\')
                              .replace('\n', '\\n')
                              .replace('\t', '\\t')[:60])
            f.write(f'DS_{idx:<4} 0x{key:02x}   0x{s:02x}    "{preview}"\n')
    return path

# ================= 词法 =================
def _skip_str_or_comment(s, i):
    n = len(s)
    if i >= n: return i
    c = s[i]
    if c == '/' and i+1 < n:
        if s[i+1] == '/':
            e = s.find('\n', i); return n if e < 0 else e+1
        if s[i+1] == '*':
            e = s.find('*/', i+2); return n if e < 0 else e+2
    if c in '"\'':
        q = c; i += 1
        while i < n:
            if s[i] == '\\': i += 2; continue
            if s[i] == q: return i+1
            i += 1
        return n
    return i

def _skip_ws_comments(s, i):
    n = len(s)
    while i < n:
        if s[i] in ' \t\r\n': i += 1; continue
        j = _skip_str_or_comment(s, i)
        if j > i: i = j; continue
        break
    return i

# ================= 结构识别 =================
def find_body_brace(s):
    i, n = 0, len(s); depth = 0; seen_eq = False
    while i < n:
        j = _skip_str_or_comment(s, i)
        if j > i: i = j; continue
        c = s[i]
        if c == '(': depth += 1
        elif c == ')': depth -= 1
        elif c == '=' and depth == 0: seen_eq = True
        elif c == '{':
            if depth == 0 and not seen_eq: return i
            d = 1; i += 1
            while i < n and d:
                k = _skip_str_or_comment(s, i)
                if k > i: i = k; continue
                if s[i] == '{': d += 1
                elif s[i] == '}': d -= 1
                i += 1
            continue
        i += 1
    return -1

def find_matching_brace(s, i):
    if i >= len(s) or s[i] != '{': return -1
    d = 1; i += 1; n = len(s)
    while i < n:
        k = _skip_str_or_comment(s, i)
        if k > i: i = k; continue
        if s[i] == '{': d += 1
        elif s[i] == '}':
            d -= 1
            if d == 0: return i
        i += 1
    return -1

def find_top_level_eq(s):
    depth = 0; i = 0; n = len(s)
    while i < n:
        k = _skip_str_or_comment(s, i)
        if k > i: i = k; continue
        c = s[i]
        if c in '([{': depth += 1
        elif c in ')]}': depth -= 1
        elif c == '=' and depth == 0: return i
        i += 1
    return -1

# ================= 扫描 / 分类 =================
def read_preprocessor(s, start):
    i = start; n = len(s)
    while i < n:
        eol = s.find('\n', i)
        if eol < 0: return n
        k = eol - 1
        while k >= i and s[k] in ' \t\r': k -= 1
        if k >= i and s[k] == '\\': i = eol + 1; continue
        return eol + 1
    return n

def read_conditional(s, start):
    i = start; n = len(s); depth = 0
    while i < n:
        eol = s.find('\n', i)
        if eol < 0: eol = n
        line = s[i:eol].lstrip()
        while eol < n and s[eol-1] == '\\':
            ne = s.find('\n', eol+1)
            if ne < 0: eol = n; break
            eol = ne
        if line.startswith('#'):
            m = re.match(r'#\s*(\w+)', line)
            if m:
                d = m.group(1)
                if d in ('if','ifdef','ifndef'): depth += 1
                elif d == 'endif':
                    depth -= 1
                    if depth == 0: return min(eol+1, n)
        i = eol + 1
    return n

def read_code_unit(s, start):
    i, n = start, len(s)
    paren = 0; brace = 0
    seen_eq = False; seen_body = False; body_is_func = False
    seen_paren = False
    while i < n:
        j = _skip_str_or_comment(s, i)
        if j > i: i = j; continue
        c = s[i]
        if c == '(': paren += 1; seen_paren = True
        elif c == ')': paren -= 1
        elif c == '=' and paren == 0 and brace == 0: seen_eq = True
        elif c == '{':
            if paren == 0 and not seen_eq and brace == 0:
                seen_body = True; body_is_func = seen_paren
            brace += 1
        elif c == '}':
            brace -= 1
            if brace == 0 and seen_body:
                k = _skip_ws_comments(s, i+1)
                if k < n and s[k] == ';': return k+1
                if body_is_func: return i+1
                if k < n and (s[k].isalpha() or s[k] == '_'):
                    m = k; d2 = 0
                    while m < n:
                        mk = _skip_str_or_comment(s, m)
                        if mk > m: m = mk; continue
                        if s[m] == '{': d2 += 1
                        elif s[m] == '}': d2 -= 1
                        elif s[m] == ';' and d2 == 0: return m+1
                        m += 1
                    return n
                return i+1
        elif c == ';' and paren == 0 and brace == 0:
            return i+1
        i += 1
    return n

def scan_items(src):
    items = []; i, n = 0, len(src); pending = 0
    while i < n:
        j = _skip_ws_comments(src, i)
        if j >= n:
            if pending < n: items.append(Item('empty', src[pending:]))
            break
        if src[j] == '#':
            m = re.match(r'#\s*(\w+)', src[j:])
            d = m.group(1) if m else ''
            if d in ('if','ifdef','ifndef'):
                end = read_conditional(src, j)
                items.append(Item('conditional', src[pending:end], src[j:end]))
            else:
                end = read_preprocessor(src, j)
                text = src[pending:end]; core = src[j:end]
                if d == 'include': items.append(Item('include', text, core))
                elif d == 'define': items.append(Item('define', text, core))
                elif d == 'pragma': items.append(Item('pragma', text, core))
                else: items.append(Item('preproc_other', text, core))
            pending = end; i = end
        else:
            end = read_code_unit(src, j)
            items.append(classify_code(src[pending:end], src[j:end]))
            pending = end; i = end
    if pending < n: items.append(Item('empty', src[pending:]))
    return items

def extract_var_name(s):
    s = s.strip().rstrip(';').strip()
    s = re.sub(r'\[[^\]]*\]\s*$', '', s).strip()
    eq = find_top_level_eq(s)
    if eq >= 0: s = s[:eq].strip()
    m = re.search(r'\(\s*\*\s*(\w+)\s*\)', s)
    if m: return m.group(1)
    m = re.findall(r'[A-Za-z_]\w*', s)
    return m[-1] if m else None

def extract_typedef_name(s):
    s2 = s.strip().rstrip().rstrip(';')
    m = re.match(r'.*\}\s*([A-Za-z_]\w*)\s*$', s2, re.DOTALL)
    if m: return m.group(1)
    m = re.findall(r'[A-Za-z_]\w*', s2)
    return m[-1] if m else None

def extract_struct_tag(head):
    m = re.match(r'\s*(?:typedef\s+)?(?:struct|union|enum)\s+(\w+)', head)
    return m.group(1) if m else None

def extract_define_name(core):
    m = re.match(r'#\s*define\s+(\w+)', core)
    return m.group(1) if m else None

def _is_func_body(head):
    depth = 0; has = False
    for c in head:
        if c == '(': depth += 1; has = True
        elif c == ')': depth -= 1
    return has and depth == 0

def _extract_real_func_name(sig_text):
    """提取真实函数名；v2.6.8 剥离末尾 __attribute__((...))。"""
    s = sig_text.rstrip()
    while s and s[-1] in ';\n\r\t ':
        s = s[:-1]
    # 【新增】剥离末尾 attribute（可能多个）
    while True:
        m = re.search(r'\s*__attribute__\s*\(\(.*?\)\)\s*$', s, re.DOTALL)
        if not m:
            break
        s = s[:m.start()].rstrip()
    if not s.endswith(')'):
        return None
    depth = 0; i = len(s) - 1
    while i >= 0:
        c = s[i]
        if c == ')':
            depth += 1
        elif c == '(':
            depth -= 1
            if depth == 0:
                break
        i -= 1
    if i < 0:
        return None
    j = i - 1
    while j >= 0 and s[j] in ' \t\r\n':
        j -= 1
    if j < 0 or not (s[j].isalnum() or s[j] == '_'):
        return None
    k = j
    while k >= 0 and (s[k].isalnum() or s[k] == '_'):
        k -= 1
    return s[k+1:j+1]

def _looks_like_func_decl(s):
    if '=' in s: return False
    if re.search(r'\(\s*\*\s*\w+\s*\)', s): return False
    return bool(re.search(r'\b[A-Za-z_]\w*\s*\(', s))

def classify_code(text, core):
    s = core.strip()
    if not s: return Item('empty', text, core)
    is_static = bool(re.match(r'\s*static\b', s))
    is_extern = bool(re.match(r'\s*extern\b', s))
    if re.match(r'\s*typedef\b', s):
        it = Item('typedef', text, core); it.name = extract_typedef_name(s)
        it.is_static = is_static; return it
    brace = find_body_brace(s)
    if brace >= 0:
        head = s[:brace].strip()
        if _is_func_body(head):
            name = _extract_real_func_name(head)
            it = Item('func_def', text, core); it.name = name
            it.is_static = is_static; it.signature = head
            end = find_matching_brace(s, brace)
            it.body = s[brace:end+1] if end > 0 else ''
            return it
        it = Item('struct_def', text, core); it.name = extract_struct_tag(head)
        it.is_static = is_static; return it
    if is_extern:
        it = Item('extern_decl', text, core)
        if '(' in s:
            it.name = _extract_real_func_name(s)
        else:
            it.name = extract_var_name(s)
        return it
    if _looks_like_func_decl(s):
        it = Item('func_decl', text, core)
        it.name = _extract_real_func_name(s)
        it.is_static = is_static; return it
    it = Item('global', text, core); it.name = extract_var_name(s)
    it.is_static = is_static; return it

# ================= static 去除 =================
def strip_static_any(text):
    i, n = 0, len(text)
    while i < n:
        j = _skip_ws_comments(text, i)
        if j > i: i = j; continue
        break
    if text.startswith('static', i) and (i+6 >= n or not text[i+6].isalnum()):
        return text[:i] + text[i+6:].lstrip()
    return text

def _add_hidden_visibility(text):
    if not text: return text
    i, n = 0, len(text)
    while i < n and text[i] in ' \t\n\r':
        i += 1
    return text[:i] + '__attribute__((visibility("hidden"))) ' + text[i:]

# ================= 依赖 / 分组 =================
def scan_identifiers(text):
    ids = set(); i, n = 0, len(text)
    while i < n:
        j = _skip_str_or_comment(text, i)
        if j > i: i = j; continue
        c = text[i]
        if c.isalpha() or c == '_':
            k = i + 1
            while k < n and (text[k].isalnum() or text[k] == '_'): k += 1
            name = text[i:k]
            if name not in KEYWORDS: ids.add(name)
            i = k
        else: i += 1
    return ids

def analyze_deps(items):
    symbols = {}
    for idx, it in enumerate(items):
        if it.name and it.kind in ('func_def','global','typedef','struct_def',
                                    'define','extern_decl','func_decl'):
            symbols[it.name] = idx
    for it in items:
        if not it.name: continue
        text = (it.signature or '') + ' ' + (it.body or '') if it.kind == 'func_def' else it.core
        for ident in scan_identifiers(text):
            if ident in symbols and ident != it.name:
                it.refs.add(ident)
    return symbols

DECL_KINDS = {'include','define','pragma','preproc_other','typedef',
              'struct_def','extern_decl','func_decl','conditional'}

def apply_map(items, mapping):
    name2g = {}
    for k, v in mapping.items():
        if isinstance(v, list):
            for n in v: name2g[n] = k
        else: name2g[k] = v
    for it in items:
        if it.name and it.name in name2g: it.group = name2g[it.name]

def group_by_prefix(items, sep, idx, main_g):
    for it in items:
        if it.group: continue
        if it.kind == 'func_def' and it.name == 'main':
            it.group = main_g; continue
        if it.kind == 'func_def' and it.name:
            parts = it.name.split(sep)
            it.group = sep.join(parts[:idx+1]) if len(parts) > idx else 'misc'

def assign_remaining(items, common_g, main_g):
    for it in items:
        if it.group: continue
        if it.kind in DECL_KINDS: it.group = common_g
        elif it.kind == 'global': it.group = common_g
        elif it.kind == 'func_def':
            it.group = main_g if it.name == 'main' else 'misc'
        else: it.group = common_g

def compute_edges(items, symbols):
    group_deps = {}; users = {}
    for it in items:
        if not it.group: continue
        for r in it.refs:
            j = symbols.get(r)
            if j is None: continue
            jt = items[j]
            if not jt.group: continue
            if jt.group != it.group:
                group_deps.setdefault(it.group, set()).add(jt.group)
                users.setdefault(r, set()).add(it.group)
    name_export = {}
    for it in items:
        if not it.name: continue
        if users.get(it.name, set()) - {it.group}:
            name_export[it.name] = True
        elif not it.is_static and it.kind in ('func_def','global'):
            name_export[it.name] = True
    for it in items:
        if it.name and it.name in name_export:
            it.export = name_export[it.name]
    return group_deps

def merge_sccs(groups, deps):
    g = {x: x for x in groups}
    def find(x):
        while g[x] != x: g[x] = g[g[x]]; x = g[x]
        return x
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb: g[ra] = rb
    for a, bs in deps.items():
        for b in bs:
            if b in deps and a in deps.get(b, ()): union(a, b)
    return {x: find(x) for x in groups}

# ================= 混淆 =================
def _rand16(rng):
    return ''.join(rng.choices(string.ascii_letters + string.digits, k=16))

def obfuscate_names(names, seed=None):
    rng = random.Random(seed) if seed is not None else random.Random()
    used = set(); result = {}
    for name in names:
        while True:
            stem = _rand16(rng)
            if stem not in used: used.add(stem); break
        result[name] = stem + ('.' + name.rsplit('.', 1)[1] if '.' in name else '')
    return result

STD_LIB_SYMBOLS = set("""
printf fprintf sprintf snprintf vprintf vfprintf vsprintf vsnprintf
puts fputs putc putchar fputc getchar fgetc gets fgets getc ungetc
fopen fclose fread fwrite fseek ftell rewind fflush feof ferror fileno
perror setvbuf malloc calloc realloc free
strlen strcpy strncpy strcat strncat strcmp strncmp strcoll strxfrm
strstr strchr strrchr strdup strndup strtok strerror
strtol strtoul strtoll strtoull strtod strtof strtold atoi atol atoll atof
memcpy memmove memset memcmp memchr
time localtime localtime_r gmtime gmtime_r strftime mktime difftime
clock ctime asctime qsort bsearch
isdigit isalpha isalnum isspace isupper islower ispunct isxdigit iscntrl
isgraph isprint toupper tolower
exit abort atexit at_quick_exit quick_exit _Exit
system getenv setenv unsetenv putenv
va_start va_arg va_end va_copy
stdin stdout stderr errno
""".split())

RESERVED = KEYWORDS | {'main', '__attribute__', '__asm__', '__inline__',
                       '__restrict__', '__extension__', '__typeof__'}

def obfuscate_symbols(items, seed=None, skip_export=False):
    rng = random.Random(seed) if seed is not None else random.Random()
    candidates = set()
    for it in items:
        if not it.name: continue
        if it.kind in ('extern_decl', 'func_decl'): continue
        if it.kind not in ('func_def','global','typedef','struct_def','define'): continue
        if it.name in RESERVED or it.name in STD_LIB_SYMBOLS: continue
        if len(it.name) < 2: continue
        if re.search(r'_(PUBLIC|API|EXPORT|DECL|CALL|INLINE)$', it.name): continue
        if skip_export:
            if it.kind == 'define': continue
            if not it.is_static: continue
        candidates.add(it.name)
    result = {}; used = set()
    first_chars = string.ascii_lowercase + '_'
    rest_chars = string.ascii_letters + string.digits
    for name in sorted(candidates):
        while True:
            cand = rng.choice(first_chars) + ''.join(rng.choices(rest_chars, k=15))
            if cand in used or cand in RESERVED: continue
            used.add(cand); break
        result[name] = cand
    return result

def _add_internal_syms(sym_map, names, seed, salt, items):
    existing_src = {it.name for it in items if it.name}
    rng = random.Random((seed or 0) ^ salt)
    used = set(sym_map.values()) | set(sym_map.keys())
    first_chars = string.ascii_lowercase + '_'
    rest_chars  = string.ascii_letters + string.digits
    for name in names:
        if name in sym_map: continue
        if name in existing_src: continue
        if name in RESERVED: continue
        while True:
            cand = rng.choice(first_chars) + ''.join(rng.choices(rest_chars, k=15))
            if cand in used or cand in RESERVED: continue
            used.add(cand); break
        sym_map[name] = cand

def apply_symbol_map(text, sym_map):
    if not sym_map: return text
    out = []; i, n = 0, len(text)
    while i < n:
        j = _skip_str_or_comment(text, i)
        if j > i:
            out.append(text[i:j]); i = j; continue
        c = text[i]
        if c.isalpha() or c == '_':
            k = i + 1
            while k < n and (text[k].isalnum() or text[k] == '_'): k += 1
            out.append(sym_map.get(text[i:k], text[i:k])); i = k
        else:
            out.append(c); i += 1
    return ''.join(out)

# ================= 字符串加密 =================
def process_strings_in_items(items, seed=None, krot=None, rng=None):
    if rng is None:
        rng = random.Random(seed) if seed is not None else random.Random()
    if krot is None: krot = _gen_krot(rng)
    assert len(krot) == 16

    instances = []; unique = {}
    for ii, it in enumerate(items):
        if it.kind != 'func_def': continue
        it.text = merge_adjacent_strings(it.text)
        for (start, end, content, is_init) in _find_string_positions(it.text):
            if is_init: continue
            if is_adjacent_concat(it.text, start, end): continue
            instances.append((ii, start, end, content))
            if content not in unique: unique[content] = len(unique)
    if not unique: return {}, {}

    encrypted = {}
    for content, idx in unique.items():
        encrypted[idx] = _encrypt_one(content, rng, krot)

    by_item = defaultdict(list)
    for (ii, start, end, content) in instances:
        by_item[ii].append((start, end, unique[content]))
    for ii, occ in by_item.items():
        text = items[ii].text; occ.sort(key=lambda x: -x[0])
        for (start, end, idx) in occ:
            text = text[:start] + f'DS_{idx}' + text[end:]
        items[ii].text = text
    return unique, encrypted

def process_global_string_arrays(items, unique, encrypted, krot, rng):
    """v2.6.8：先合并相邻字符串 + 正则支持 char * const[] / char **[]"""
    results = []
    pat = re.compile(
        r'^(\s*(?:static\s+)?(?:const\s+)?char\s*(?:\*+\s*|\bconst\s+)*)'
        r'([A-Za-z_]\w*)\s*\[\s*(\d*)\s*\]\s*=\s*\{(.*)\}\s*;\s*$',
        re.DOTALL)
    for ii, it in enumerate(items):
        if it.kind != 'global':
            continue
        # P0-2：先合并相邻字符串，避免 "a" "b" 被拆成两个 NULL
        merged = merge_adjacent_strings(it.text)
        if merged != it.text:
            it.text = merged
            it.core = merged
        s = it.text.strip()
        m = pat.match(s)
        if not m:
            continue
        prefix, name, size, init_body = m.groups()
        occs = extract_string_literals(init_body)
        if not occs:
            continue
        ds_ids = []
        new_body = init_body
        repls = []
        for (start, end, content) in occs:
            if content not in unique:
                unique[content] = len(unique)
                encrypted[unique[content]] = _encrypt_one(content, rng, krot)
            ds_id = unique[content]
            ds_ids.append(ds_id)
            repls.append((start, end, ds_id))
        for (start, end, ds_id) in sorted(repls, key=lambda x: -x[0]):
            new_body = new_body[:start] + 'NULL' + new_body[end:]
        if init_body in it.text:
            it.text = it.text.replace(init_body, new_body, 1)
            it.core = it.text
        results.append(dict(item_idx=ii, name=name,
                            size=size, has_size=bool(size),
                            ds_ids=ds_ids, group=it.group))
    return results

def process_file_signatures(groups, unique, encrypted, krot, rng):
    """为每个 group 生成 16B sentinel + FNV-1a 64 hash（hex 字符串）。"""
    result = {}
    for g in sorted(groups):
        sentinel = bytes(rng.randint(0, 255) for _ in range(16))
        h = 0xcbf29ce484222325
        for b in sentinel:
            h ^= b
            h = (h * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
        hex_str = f'{h:016x}'
        if hex_str not in unique:
            unique[hex_str] = len(unique)
            encrypted[unique[hex_str]] = _encrypt_one(hex_str, rng, krot)
        result[g] = {'sentinel': sentinel, 'ds_id': unique[hex_str]}
    return result

def _fscheck_block(group_name, sig_info, ctor_base=201):
    if not sig_info:
        return []
    safe_g = re.sub(r'\W', '_', group_name)
    sentinel = sig_info['sentinel']
    ds_id    = sig_info['ds_id']
    sent_str = ', '.join(f'0x{b:02x}' for b in sentinel)
    return [
        '/* auto-generated: file signature check */',
        f'static volatile const unsigned char _fsig_{safe_g}[16] = {{ {sent_str} }};',
        '',
        f'__attribute__((noinline, constructor({ctor_base})))',
        f'static void _fscheck_{safe_g}(void) {{',
        '    unsigned long long h = 0xcbf29ce484222325ULL;',
        f'    for (int i = 0; i < 16; i++) {{ h ^= _fsig_{safe_g}[i]; h *= 0x100000001b3ULL; }}',
        f'    char *p = ds_get({ds_id});',
        '    unsigned long long exp = 0;',
        '    for (int i = 0; i < 16; i++) {',
        "        int v = (p[i] <= '9') ? (p[i] - '0') : (p[i] - 'a' + 10);",
        '        exp = (exp << 4) | (unsigned long long)v;',
        '    }',
        '    if (h != exp) _Exit(4);',
        '}',
        '',
    ]

# ================= C 代码生成器 =================
def normalize_sig(sig):
    out = []; i = 0; n = len(sig); ws = False
    while i < n:
        if sig[i] in '"\'':
            q = sig[i]; j = i+1
            while j < n:
                if sig[j] == '\\': j += 2; continue
                if sig[j] == q: j += 1; break
                j += 1
            out.append(sig[i:j]); i = j; ws = False
        elif sig[i] in ' \t\r\n':
            if not ws: out.append(' '); ws = True
            i += 1
        else:
            out.append(sig[i]); i += 1; ws = False
    return ''.join(out).strip()

def extern_decl_of(global_text):
    i, n = 0, len(global_text)
    while i < n:
        j = _skip_ws_comments(global_text, i)
        if j > i: i = j; continue
        break
    s = global_text[i:]
    s = re.sub(r'^static\s+', '', s)
    eq = find_top_level_eq(s)
    if eq >= 0: s = s[:eq]
    s = s.rstrip().rstrip(';').strip()
    return 'extern ' + s + ';' if s else None

def _write(outdir, fname, text, sym_map):
    text = apply_symbol_map(text, sym_map)
    with open(os.path.join(outdir, fname), 'w') as f:
        f.write(text)

def gen_decrypt_h(outdir, fname, count, sym_map=None, guard='CSPLIT_DECRYPT_H'):
    L = ['/* auto-generated */',
         f'#ifndef {guard}', f'#define {guard}', '',
         'char* ds_get(int n);', '']
    for idx in range(count):
        L.append(f'#define DS_{idx} ds_get({idx})')
    L += ['', '#endif', '']
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map or {})

def gen_decrypt_c(outdir, fname, unique_strings, encrypted_data, krot,
                  sym_map=None, seed=None):
    assert len(krot) == 16
    N = len(unique_strings)
    if N == 0:
        with open(os.path.join(outdir, fname), 'w') as f:
            f.write('/* empty */\n')
        return

    orig_off, orig_len, orig_key, orig_seed, orig_data = [], [], [], [], []
    max_len = 1
    for i in range(N):
        enc, key, s = encrypted_data[i]
        orig_off.append(len(orig_data)); orig_len.append(len(enc))
        orig_key.append(key); orig_seed.append(s)
        orig_data.extend(enc)
        if len(enc) > max_len: max_len = len(enc)

    rng_idx = random.Random(((seed or 0) ^ 0x5EC4) & 0xFFFFFFFF)
    P = list(range(N))
    rng_idx.shuffle(P)
    inv_P = [0] * N
    for i in range(N):
        inv_P[P[i]] = i

    ds_off = [0] * N; ds_len = [0] * N
    ds_key = [0] * N; ds_seed = [0] * N; ds_data = []
    for j in range(N):
        i = inv_P[j]
        ds_off[j] = len(ds_data)
        ds_len[j] = orig_len[i]
        ds_key[j] = orig_key[i]
        ds_seed[j] = orig_seed[i]
        ds_data.extend(orig_data[orig_off[i]:orig_off[i] + orig_len[i]])

    def fmt_bytes(bs):
        if not bs: return '    0'
        return '\n'.join('    ' + ', '.join(f'0x{b:02x}' for b in bs[i:i+16]) + ','
                         for i in range(0, len(bs), 16))
    def fmt_ints(xs):
        if not xs: return '    0'
        return '\n'.join('    ' + ', '.join(str(x) for x in xs[i:i+16]) + ','
                         for i in range(0, len(xs), 16))

    krot_str = ', '.join(f'0x{b:02x}' for b in krot)
    perm_str = ', '.join(str(p) for p in P)

    L = [
        '/* auto-generated — decrypt v2.6.6 (6-layer) */', '',
        f'static const unsigned char ds_data[{max(len(ds_data),1)}] = {{',
        fmt_bytes(ds_data), '};', '',
        f'static const int ds_off[{N}] = {{', fmt_ints(ds_off), '};', '',
        f'static const int ds_len[{N}] = {{', fmt_ints(ds_len), '};', '',
        f'static const unsigned char ds_key[{N}] = {{',
        '    ' + ', '.join(f'0x{k:02x}' for k in ds_key), '};', '',
        f'static const unsigned char ds_seed[{N}] = {{',
        '    ' + ', '.join(f'0x{k:02x}' for k in ds_seed), '};', '',
        f'static const int ds_idx_pos[{N}] = {{', '    ' + perm_str, '};', '',
        f'static char ds_buf[{N}][{max_len+1}];', '',
        '__attribute__((noinline, used))',
        'char* ds_get(int n) {',
        f'    static const unsigned char kRot[16] = {{ {krot_str} }};',
        '    int r = ds_idx_pos[n];',
        '    int off = ds_off[r], len = ds_len[r];',
        '    unsigned char key = ds_key[r];',
        '    unsigned char s   = ds_seed[r];',
        # v2.6.6: 用 volatile 防止编译器优化掉清零
        '    for (int i = 0; i < len + 1; i++) ((volatile char*)ds_buf[n])[i] = 0;',
        '    for (int i = 0; i < len; i++) {',
        '        unsigned char v = ds_data[off + i];',
        '        unsigned char k1 = (unsigned char)(kRot[(i + s) & 0xF] ^ (i * 37));',
        '        unsigned char k2 = (unsigned char)(kRot[(i * 3 + s + 7) & 0xF] ^ ((i * 91 + 13) & 0xFF));',
        '        v = (unsigned char)(v - key);',
        '        v = (unsigned char)((v << 5) | (v >> 3));',
        '        v ^= k2;',
        '        v = (unsigned char)(v - k1);',
        '        v = (unsigned char)((v >> 3) | (v << 5));',
        '        v ^= key;',
        '        ds_buf[n][i] = (char)v;',
        '    }',
        '    ds_buf[n][len] = 0;',
        '    return ds_buf[n];',
        '}', '',
        '__attribute__((noinline, used))',
        'void _ds_warm(void) {',
        f'    for (int i = 0; i < {N}; i++) (void)ds_get(i);',
        '}', ''
    ]
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map or {})

# ================= Anti-Debug =================
def gen_antidebug_h(outdir, fname, sym_map=None):
    guard = 'CSPLIT_ADBG_H'
    L = ['/* auto-generated */',
         f'#ifndef {guard}', f'#define {guard}', '',
         'void _csplit_adbg_init(void);', '',
         '#endif', '']
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map or {})

def gen_antidebug_c(outdir, fname, sym_map=None,
                    features=None, adbg_priority=65535):
    """anti-debug v2.6.8 — features 动态、priority 可调、Termux-safe"""
    if not features:
        features = ['frida-agent', 'libfrida-', 'gdb-server', 'libhook', 'frida']

    def enc(s, k): return [b ^ k for b in s]

    E = {
        '_a_pst':  (b'/proc/self/status',   0x13),
        '_a_pmp':  (b'/proc/self/maps',     0x37),
        '_a_fmt':  (b'TracerPid: %d',       0x5A),
        '_a_fhk':  (b'libhook',             0x61),
        '_a_fr':   (b'frida',               0x24),
        '_a_noad': (b'CSPLIT_NO_ADBG',      0x4D),
        '_a_dbg':  (b'CSPLIT_ADBG_DEBUG',   0x2C),
        '_a_pre':  (b'LD_PRELOAD',          0x5C),
        '_a_mhit': (b'[adbg] maps hit: %s',  0x6E),
        '_a_mno':  (b'[adbg] no %s\n',       0x5D),
        '_a_mtp':  (b'[adbg] TracerPid=%d\n', 0x2F),
        '_a_mld':  (b'[adbg] LD_PRELOAD=%s\n', 0x3A),
        '_a_nul':  (b'(null)',               0x6B),
    }

    feat_entries = []
    for idx, feat in enumerate(features):
        key = ((0x20 + idx * 0x11) & 0xFF) or 0x42
        name = f'_a_ft{idx}'
        feat_entries.append((name, feat.encode(), key))

    def arr(name, bs):
        return (f'static const unsigned char {name}[{len(bs)}] = {{'
                + ', '.join(f'0x{b:02x}' for b in bs) + '};')

    L = [
        '/* auto-generated — anti-debug v2.6.8 (Termux-safe) */',
        '#include <stdio.h>',
        '#include <stdlib.h>',
        '#include <string.h>',
        '#include <unistd.h>',
        '',
    ]
    for name, (s, k) in E.items():
        L.append(arr(name, enc(s, k)))
    for name, data, k in feat_entries:
        L.append(arr(name, [b ^ k for b in data]))
    L.append('')

    for name in E:
        sz = max(len(enc(*E[name])), 32) + 4
        L.append(f'static char _b{name}[{sz}];')
    for name, data, k in feat_entries:
        sz = max(len(data), 32) + 4
        L.append(f'static char _b{name}[{sz}];')
    L.append('static int _a_state = -1;')
    L.append('')
    L.append('__attribute__((noinline))')
    L.append('static void _a_dec(unsigned char *d, const unsigned char *s,')
    L.append('                   int n, unsigned char k) {')
    L.append('    volatile unsigned char t;')
    L.append('    for (int i = 0; i < n; i++) { t = s[i]; d[i] = (char)(t ^ k); }')
    L.append('    d[n] = 0;')
    L.append('}')
    L.append('')
    L.append(f'__attribute__((constructor({adbg_priority})))')
    L.append('static void _a_probe(void) {')
    L.append('    volatile int dbg = 0;')
    for name, (s, k) in E.items():
        L.append(f'    _a_dec((unsigned char*)_b{name}, {name}, '
                 f'sizeof({name}), 0x{k:02x});')
    for name, data, k in feat_entries:
        L.append(f'    _a_dec((unsigned char*)_b{name}, {name}, '
                 f'sizeof({name}), 0x{k:02x});')
    L.append('')
    L.append('    const char *v1 = getenv(_b_a_noad);')
    L.append('    const char *v2 = getenv(_b_a_dbg);')
    L.append('    int disabled = (v1 && v1[0] == \'1\');')
    L.append('    int debug    = (v2 && v2[0] == \'1\');')
    L.append('    _a_state = disabled ? 1 : 0;')
    L.append('    if (disabled) return;')
    L.append('')
    # TracerPid
    L.append('    FILE *f = fopen(_b_a_pst, "r");')
    L.append('    if (f) {')
    L.append('        char buf[256]; int pid = 0;')
    L.append('        while (fgets(buf, sizeof(buf), f))')
    L.append('            if (sscanf(buf, _b_a_fmt, &pid) == 1) break;')
    L.append('        fclose(f);')
    L.append('        if (debug) fprintf(stderr, _b_a_mtp, pid);')
    L.append('        if (pid != 0) _Exit(1);')
    L.append('    } else if (debug) {')
    L.append('        fprintf(stderr, _b_a_mno, _b_a_pst);')
    L.append('    }')
    L.append('')
    # maps（动态 features）
    if feat_entries:
        L.append('    f = fopen(_b_a_pmp, "r");')
        L.append('    if (f) {')
        L.append('        char buf[1024]; int hit = 0;')
        L.append('        while (fgets(buf, sizeof(buf), f)) {')
        conds = [f'strstr(buf, _b{name})' for name, _, _ in feat_entries]
        if len(conds) == 1:
            L.append(f'            if ({conds[0]}) {{')
        else:
            L.append(f'            if ({conds[0]}')
            for c in conds[1:]:
                L.append(f'                || {c}')
            L.append('            ) {')
        L.append('                if (debug) fprintf(stderr, _b_a_mhit, buf);')
        L.append('                hit = 1; break;')
        L.append('            }')
        L.append('        }')
        L.append('        fclose(f);')
        L.append('        if (hit) _Exit(2);')
        L.append('    } else if (debug) {')
        L.append('        fprintf(stderr, _b_a_mno, _b_a_pmp);')
        L.append('    }')
        L.append('')
    # LD_PRELOAD（固定 frida / libhook）
    L.append('    const char *lp = getenv(_b_a_pre);')
    L.append('    if (debug) fprintf(stderr, _b_a_mld, lp ? lp : _b_a_nul);')
    L.append('    if (lp && (strstr(lp, _b_a_fhk) || strstr(lp, _b_a_fr))) _Exit(3);')
    L.append('}')
    L.append('')
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map or {})

# ================= 通用/组/入口生成 =================
def gen_common_h(items, outdir, fname, sym_map,
                 decrypt_h_name=None, adbg_h_name=None, junk_h_names=None):
    L = ['/* auto-generated */',
         '#ifndef CSPLIT_COMMON_H', '#define CSPLIT_COMMON_H', '']
    if decrypt_h_name: L.append(f'#include "{decrypt_h_name}"'); L.append('')
    if adbg_h_name:    L.append(f'#include "{adbg_h_name}"');    L.append('')
    if junk_h_names:
        for jh in junk_h_names:
            L.append(f'#include "{jh}"')
        L.append('')

    export_names = {it.name for it in items if it.export and it.name}

    for it in items:
        if it.group == 'common' and it.kind not in ('empty', 'func_def', 'global'):
            txt = it.text.rstrip()
            if it.kind == 'func_decl' and it.name in export_names:
                txt = strip_static_any(txt)
                txt = _add_hidden_visibility(txt)
            L.append(txt)

    for it in items:
        if it.kind == 'func_def' and it.export and it.name != 'main':
            L.append(re.sub(r'^static\s+', '', normalize_sig(it.signature)) + ';')

    for it in items:
        if it.kind == 'global' and it.export:
            d = extern_decl_of(it.text)
            if d: L.append(d)

    L += ['', '#endif', '']
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map)

def _gsinit_block(global_arrays, group_name, ctor_base=200):
    garrs = [ga for ga in (global_arrays or []) if ga.get('group') == group_name]
    if not garrs:
        return []
    L = ['/* auto-generated: global string init */',
         f'__attribute__((constructor({ctor_base})))',
         f'static void _gsinit__{re.sub(r"[^A-Za-z0-9_]", "_", group_name)}(void) {{']
    for ga in garrs:
        for i, ds_id in enumerate(ga['ds_ids']):
            L.append(f'    {ga["name"]}[{i}] = ds_get({ds_id});')
    L += ['}', '']
    return L

def gen_common_c(items, outdir, fname, common_h_name, sym_map,
                 global_arrays=None, file_sigs=None, ctor_base=200):
    proto_lines = []; body = []
    for it in items:
        if it.group != 'common': continue
        if it.kind == 'func_def':
            sig = normalize_sig(it.signature)
            if it.export: sig = re.sub(r'^static\s+', '', sig)
            if it.name != 'main': proto_lines.append(sig + ';')
            txt = it.text.rstrip()
            if it.export and it.is_static:
                txt = strip_static_any(txt)
                txt = _add_hidden_visibility(txt)
            body.append(txt); body.append('')
        elif it.kind == 'global':
            txt = it.text.rstrip()
            if it.export and it.is_static:
                txt = strip_static_any(txt)
                txt = _add_hidden_visibility(txt)
            body.append(txt); body.append('')
    if not body: return False
    L = ['/* auto-generated: common */', f'#include "{common_h_name}"']
    if file_sigs and 'common' in file_sigs:
        L.append('#include <stdlib.h>')
    L.append('')
    if proto_lines:
        L.extend(proto_lines); L.append('')
    L.extend(body)
    L.extend(_gsinit_block(global_arrays, 'common', ctor_base))
    if file_sigs and 'common' in file_sigs:
        L.extend(_fscheck_block('common', file_sigs['common'], ctor_base + 1))
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map)
    return True

def gen_group_h(g, items, group_deps, outdir, fname, file_map, sym_map):
    common_h = file_map.get('common.h', 'common.h')
    guard = 'CSPLIT_' + re.sub(r'\W', '_', g).upper() + '_H'
    L = [f'/* auto-generated: {g} */',
         f'#ifndef {guard}', f'#define {guard}', '',
         f'#include "{common_h}"']
    for d in sorted(group_deps.get(g, ())):
        if d not in ('common', g):
            L.append(f'#include "{file_map.get(f"{d}.h", f"{d}.h")}"')
    L.append('')
    for it in items:
        if it.group != g: continue
        if it.kind == 'func_def' and it.export and it.name != 'main':
            sig = re.sub(r'^static\s+', '', normalize_sig(it.signature))
            if it.is_static:
                sig = '__attribute__((visibility("hidden"))) ' + sig
            L.append(sig + ';')
        elif it.kind == 'global' and it.export:
            d = extern_decl_of(it.text)
            if d:
                if it.is_static:
                    d = '__attribute__((visibility("hidden"))) ' + d
                L.append(d)
    L += ['', '#endif', '']
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map)

def gen_group_c(g, items, outdir, fname, gh_name, sym_map,
                global_arrays=None, file_sigs=None, ctor_base=200):
    L = [f'/* auto-generated: {g} */', f'#include "{gh_name}"']
    if file_sigs and g in file_sigs:
        L.append('#include <stdlib.h>')
    L.append('')
    for it in items:
        if it.group != g or it.kind == 'empty': continue
        txt = it.text.rstrip()
        if it.export and it.is_static and it.kind in ('func_def','global'):
            txt = strip_static_any(txt)
            txt = _add_hidden_visibility(txt)
        L.append(txt); L.append('')
    L.extend(_gsinit_block(global_arrays, g, ctor_base))
    if file_sigs and g in file_sigs:
        L.extend(_fscheck_block(g, file_sigs[g], ctor_base + 1))
    _write(outdir, fname, '\n'.join(L) + '\n', sym_map)

# ================= 环境检测 / Makefile / Standalone =================
def detect_ldflags(items):
    flags = set()
    for it in items:
        t = it.core
        if 'curl_easy' in t or 'curl/curl.h' in t: flags.add('-lcurl')
        if 'pthread_' in t or 'pthread.h' in t: flags.add('-lpthread')
        if ('openssl/' in t or re.search(r'\bSSL_CTX\b', t)
            or re.search(r'\bOPENSSL_', t) or re.search(r'\bEVP_[A-Z]', t)):
            flags |= {'-lssl','-lcrypto'}
        if 'M_PI' in t or re.search(r'\b(sqrt|pow|sin|cos|exp|log)\s*\(', t):
            flags.add('-lm')
        if 'zlib.h' in t or re.search(r'\bcompress\s*\(', t): flags.add('-lz')
        if 'sqlite3_' in t or 'sqlite3.h' in t: flags.add('-lsqlite3')
    return ' '.join(sorted(flags))

def gen_makefile(outdir, ldflags, elf_name, cflags_extra='', ldflags_extra='',
                 src_dir_rel='..'):
    with open(os.path.join(outdir, 'Makefile'), 'w') as f:
        f.write(f"""# auto-generated by csplit.py
CC       ?= cc
OBJCOPY  ?= objcopy
SRC_DIR  ?= {src_dir_rel}
CFLAGS   ?= -O2 -Wall -Wno-format-security -I. -I$(SRC_DIR){cflags_extra}
DEPFLAGS := -MMD -MP
LDFLAGS  ?= {ldflags}{ldflags_extra}

SRC      := $(wildcard *.c)
OBJ      := $(SRC:.c=.o)
DEP      := $(SRC:.c=.d)
TARGET   := {elf_name}

all: $(TARGET)

$(TARGET): $(OBJ)
\t$(CC) $(CFLAGS) $(OBJ) -o $@.tmp $(LDFLAGS)
\t$(OBJCOPY) --remove-section=.comment --remove-section=.note.gnu.build-id $@.tmp $@
\trm -f $@.tmp

%.o: %.c
\t$(CC) $(CFLAGS) $(DEPFLAGS) -c $< -o $@

-include $(DEP)

clean:
\trm -f $(OBJ) $(DEP) $(TARGET)

.PHONY: all clean
""")

def gen_makefile_lib(outdir, ldflags, elf_name, cflags_extra='', ldflags_extra='',
                     src_dir_rel='..'):
    with open(os.path.join(outdir, 'Makefile'), 'w') as f:
        f.write(f"""# auto-generated by csplit.py (library mode)
CC       ?= cc
SRC_DIR  ?= {src_dir_rel}
CFLAGS   ?= -O2 -Wall -Wno-format-security -I. -I$(SRC_DIR) -fPIC{cflags_extra}
DEPFLAGS := -MMD -MP
LDFLAGS  ?= {ldflags} -shared{ldflags_extra}

SRC      := $(wildcard *.c)
OBJ      := $(SRC:.c=.o)
DEP      := $(SRC:.c=.d)
TARGET   := {elf_name}

all: $(TARGET)

$(TARGET): $(OBJ)
\t$(CC) $(OBJ) -o $@ $(LDFLAGS)

%.o: %.c
\t$(CC) $(CFLAGS) $(DEPFLAGS) -c $< -o $@

-include $(DEP)

clean:
\trm -f $(OBJ) $(DEP) $(TARGET)

.PHONY: all clean
""")

def gen_standalone(outdir, groups, group_deps, ldflags, file_map, sym_map, elf_name):
    sd = os.path.join(outdir, 'standalone'); os.makedirs(sd, exist_ok=True)
    for f in os.listdir(sd):
        try: os.remove(os.path.join(sd, f))
        except OSError: pass
    common_h = file_map.get('common.h', 'common.h')
    def closure(g, seen=None):
        if seen is None: seen = set()
        if g in seen: return seen
        seen.add(g)
        for d in group_deps.get(g, ()):
            if d not in ('common', g): closure(d, seen)
        return seen
    lines = ['#!/bin/bash', 'set -e', 'cd "$(dirname "$0")"', 'TOP=..']
    for g in sorted(groups):
        if g in ('common','main'): continue
        cl = closure(g) - {'main'}
        others = []
        for x in sorted(cl):
            if x == g: continue
            xc = file_map.get(f'{x}.c', f'{x}.c')
            others.append(f'$TOP/{xc[:-2]}.o')
        gh = file_map.get(f'{g}.h', f'{g}.h')
        gc = file_map.get(f'{g}.c', f'{g}.c')
        gobj = gc[:-2] + '.o'
        with open(os.path.join(sd, f'test_{g}.c'), 'w') as f:
            f.write(f'/* test: {g} */\n#include "{common_h}"\n'
                    f'#include "../{gh}"\n\nint main(void) {{ return 0; }}\n')
        lines.append(f'echo "== {g} =="')
        lines.append(f'$CC -I$TOP -c test_{g}.c -o test_{g}.o')
        lines.append(f'$CC test_{g}.o $TOP/{gobj} {" ".join(others)} -o {g}.elf {ldflags}')
        lines.append(f'./{g}.elf && echo "  OK"')
    lines.append('echo "all standalone tests built"')
    path = os.path.join(sd, 'run_all.sh')
    with open(path, 'w') as f: f.write('\n'.join(lines) + '\n')
    os.chmod(path, 0o755)

# ================= 验证 =================
def verify(original, outdir, cc, cflags, ldflags, elf_name='split.elf',
           cflags_extra='', ldflags_extra='', library=False):
    src_dir = os.path.dirname(os.path.abspath(original))
    if not ldflags:
        items = scan_items(_read_source_file(original))     # 改动
        ldflags = detect_ldflags(items)
    full_c = (cflags + ' ' + cflags_extra + ' -Wno-format-security').split()
    full_l = (ldflags + ' ' + ldflags_extra).split()

    oracle_o = os.path.join(outdir, '.oracle.o')
    if library:
        print('\n[1] 编译原始文件（library 模式：-c）')
        r = subprocess.run([cc] + full_c + ['-fPIC', '-I', src_dir, '-c',
                           original, '-o', oracle_o],
                           capture_output=True, text=True)
        if r.returncode:
            print('  ✗ 原文件编译失败:'); print(r.stderr); return False
        print('  ✓ OK')
    else:
        print('\n[1] 编译原始文件')
        oracle_elf = os.path.join(outdir, '.oracle.elf')
        r = subprocess.run([cc] + full_c + ['-I', src_dir,
                           original, '-o', oracle_elf] + full_l,
                           capture_output=True, text=True)
        if r.returncode:
            print('  ✗ 原文件编译失败:'); print(r.stderr); return False
        print('  ✓ OK')

    print('\n[2] 单独编译每个 .c')
    cfiles = sorted(f for f in os.listdir(outdir) if f.endswith('.c'))
    objs = []
    for cf in cfiles:
        obj = os.path.join(outdir, cf[:-2] + '.o')
        cmd = [cc] + full_c + ['-I', outdir, '-I', src_dir, '-c',
                               os.path.join(outdir, cf), '-o', obj]
        if library: cmd.insert(1, '-fPIC')
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode:
            print(f'  ✗ {cf}:'); print(r.stderr); return False
        print(f'  ✓ {cf}'); objs.append(obj)

    elf = os.path.join(outdir, elf_name)
    if library:
        print(f'\n[3] 链接为共享库 -> {elf_name}')
        r = subprocess.run([cc, '-shared'] + objs + ['-o', elf] + full_l,
                           capture_output=True, text=True)
        if r.returncode:
            print('  ✗ 链接失败:'); print(r.stderr); return False
        print(f'  ✓ {elf}')
        print(f'\n验证通过:\n  原始: {oracle_o}\n  拆分: {elf}')
    else:
        print(f'\n[3] 链接 -> {elf_name}')
        r = subprocess.run([cc] + objs + ['-o', elf] + full_l,
                           capture_output=True, text=True)
        if r.returncode:
            print('  ✗ 链接失败:'); print(r.stderr); return False
        print(f'  ✓ {elf}')
        print(f'\n验证通过:\n  原始: {os.path.join(outdir, ".oracle.elf")}\n  拆分: {elf}')
    return True

# ================= 主流程 =================
def main():
    ap = argparse.ArgumentParser(
        description='csplit.py v2.6.6',
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('input')
    ap.add_argument('-o','--output', default='split_out')
    ap.add_argument('--map')
    ap.add_argument('--split-by', default='prefix', choices=['prefix','none','map'])
    ap.add_argument('--prefix-sep', default='_')
    ap.add_argument('--prefix-idx', type=int, default=0)
    ap.add_argument('--main', default='main')
    ap.add_argument('--common', default='common')
    ap.add_argument('--verify', action='store_true')
    ap.add_argument('--standalone', action='store_true')
    ap.add_argument('--library', action='store_true',
                    help='输入是库（无 main），编译为 .so 不要求可执行文件')
    ap.add_argument('--strict-parse', action='store_true',
                    help='扫描未完整覆盖原文时直接报错退出（默认只警告）')
    ap.add_argument('--dry-run', action='store_true',
                    help='只分析不生成任何文件（用于快速验证解析）')
    ap.add_argument('--cc', default='cc')
    ap.add_argument('--cflags', default='-O2')
    ap.add_argument('--ldflags', default='')
    ap.add_argument('--obfuscate', action='store_true')
    ap.add_argument('--obfuscate-symbols', action='store_true')
    ap.add_argument('--obfuscate-target', action='store_true')
    ap.add_argument('--obfuscate-all', action='store_true')
    ap.add_argument('--encrypt-strings', action='store_true')
    ap.add_argument('--strip', action='store_true')
    ap.add_argument('--lto', action='store_true')
    ap.add_argument('--visibility-hidden', action='store_true')
    ap.add_argument('--no-unwind', action='store_true')
    ap.add_argument('--anti-debug', action='store_true')
    ap.add_argument('--seed', type=int, default=None)
    ap.add_argument('--junk', action='store_true')
    ap.add_argument('--junk-checks', type=int, default=4)
    ap.add_argument('--junk-panic-code', type=lambda x: int(x, 0), default=0xDEAD)
    ap.add_argument('--junk-files', type=int, default=1,
                    help='垃圾 C 文件数量（默认 1）；总校验点 = --junk-checks，均分到各文件')
    ap.add_argument('--constructor-base', type=int, default=200,
                    help='constructor 起始优先级（默认 200）；'
                         'gsinit=base, fscheck=base+1, junk-decoy=base+2')
    ap.add_argument('--adbg-priority', type=int, default=65535,
                    help='anti-debug constructor 优先级（默认 65535）；'
                         '若用户源码自定义了 65535 的 constructor，改此值避开冲突')
    ap.add_argument('--adbg-features', type=str,
                    default='frida-agent,libfrida-,gdb-server,libhook,frida',
                    help='anti-debug /proc/self/maps 检测特征（逗号分隔）')
    a = ap.parse_args()

    if a.obfuscate_all:
        a.obfuscate = a.obfuscate_symbols = a.obfuscate_target = True

    src = _read_source_file(a.input)
    items = scan_items(src)
    if ''.join(it.text for it in items) != src:
        msg = '[警告] 扫描未完整覆盖原文（部分代码可能被遗漏或顺序错乱）'
        if a.strict_parse:
            print(f'[错误] {msg}；--strict-parse 下拒绝继续', file=sys.stderr)
            sys.exit(2)
        else:
            print(msg, file=sys.stderr)
    symbols = analyze_deps(items)

    # ---- Junk ----
    junk_modules = []
    if a.junk:
        n_junk_files = max(1, a.junk_files)
        existing = {it.name for it in items if it.name}
        for j in range(n_junk_files):
            jk_rng = random.Random(((a.seed or 0) ^ 0xC5A1) + j * 0x9E3779B1)
            jk_table = [jk_rng.randint(0, 255) for _ in range(16)]
            jk_seed  = jk_rng.getrandbits(64)
            base  = a.junk_checks // n_junk_files
            extra = 1 if j < (a.junk_checks % n_junk_files) else 0
            n_checks_this = base + extra
            jk_expected = [_jk_compute(i, jk_seed, jk_table)
                           for i in range(n_checks_this)]
            while True:
                ck = '_z' + ''.join(random.choices(string.ascii_lowercase, k=6))
                if ck not in existing:
                    existing.add(ck); break
            while True:
                panic = '_z' + ''.join(random.choices(string.ascii_lowercase, k=6))
                if panic not in existing and panic != ck:
                    existing.add(panic); break
            basename = 'junk' if j == 0 else f'junk{j}'
            junk_modules.append({
                'basename': basename, 'ck': ck, 'panic': panic,
                'n': n_checks_this, 'seed': jk_seed,
                'table': jk_table, 'expected': jk_expected,
                'panic_code': a.junk_panic_code,
            })

        # v2.6.6: 安全注入（不硬编码 pool，兜底任意 func_def）
        pool = ['main', 'warmup', 'do_login', 'do_sign', 'parse_sign']
        n_total = sum(jm['n'] for jm in junk_modules)
        injected = inject_junk_checks_safe(items, n_total, junk_modules, pool)
        if not injected and n_total > 0:
            print(f'\n[警告] junk 校验无可用注入点（源码无任何函数），'
                  f'junk 模块仅作编译噪音', file=sys.stderr)

    if a.map:
        with open(a.map, encoding='utf-8') as f: apply_map(items, json.load(f))
    if a.split_by == 'prefix':
        group_by_prefix(items, a.prefix_sep, a.prefix_idx, a.main)
    assign_remaining(items, a.common, a.main)

    group_deps = compute_edges(items, symbols)
    groups = {it.group for it in items if it.group}
    if groups:
        rep = merge_sccs(groups, group_deps)
        for it in items:
            if it.group: it.group = rep[it.group]
        group_deps = compute_edges(items, symbols)
        groups = {it.group for it in items if it.group}

    # ---- 字符串加密 + 全局数组 + 文件签名 ----
    unique_strings, encrypted_data = {}, {}
    krot = None
    global_arrays = []
    file_sigs = {}
    if a.encrypt_strings:
        krot_rng = random.Random(a.seed) if a.seed is not None else random.Random()
        krot = _gen_krot(krot_rng)
        str_rng = random.Random(a.seed) if a.seed is not None else random.Random()
        unique_strings, encrypted_data = process_strings_in_items(
            items, a.seed, krot, rng=str_rng)
        global_arrays = process_global_string_arrays(
            items, unique_strings, encrypted_data, krot, str_rng)
        for ga in global_arrays:
            ga['group'] = items[ga['item_idx']].group

        print(f'\n== KROT（滚动密钥，16 字节）==')
        print('  ' + ', '.join(f'0x{b:02x}' for b in krot))

        if groups:
            file_sigs = process_file_signatures(
                groups, unique_strings, encrypted_data, krot, str_rng)
            if file_sigs:
                print(f'\n== 文件签名校验 ({len(file_sigs)} 个组) ==')
                for g in sorted(file_sigs):
                    print(f'  {g:<16} sentinel=16B -> DS_{file_sigs[g]["ds_id"]}')

        if global_arrays:
            print(f'\n== 全局字符串数组加密 ({len(global_arrays)} 个) ==')
            for ga in global_arrays[:5]:
                print(f'  {ga["name"]}[{len(ga["ds_ids"])}] -> group={ga["group"]}')

    has_common_defs = any(it.group == a.common and it.kind in ('global','func_def')
                          for it in items)
    all_names = ['common.h']
    if has_common_defs: all_names.append('common.c')
    if a.encrypt_strings and unique_strings: all_names += ['decrypt.h', 'decrypt.c']
    if a.anti_debug: all_names += ['adbg.h', 'adbg.c']
    if a.junk:
        for jm in junk_modules:
            all_names += [f'{jm["basename"]}.h', f'{jm["basename"]}.c']
    for g in groups:
        if g == a.common: continue
        all_names += [f'{g}.h', f'{g}.c']

    file_map = obfuscate_names(all_names, a.seed) if a.obfuscate \
               else {n: n for n in all_names}
    sym_map = obfuscate_symbols(items, a.seed, skip_export=a.library) \
              if a.obfuscate_symbols else {}
    if a.obfuscate_symbols:
        if a.encrypt_strings and unique_strings:
            _add_internal_syms(sym_map,
                ['ds_get','ds_data','ds_off','ds_len','ds_key','ds_seed',
                 'ds_buf','ds_idx_pos','kRot','_ds_warm'],
                a.seed, 0xD5, items)
        if a.junk:
            junk_internals = ['j_a','j_b','j_c','j_compute','_ck_expected',
                              '_j_dbg_name','_j_fmt',
                              '_j_buf_name','_j_buf_fmt',
                              '_j_inited','_j_debug','_j_prepare']
            for jm in junk_modules:
                junk_internals.extend([jm['ck'], jm['panic']])
                if jm['n'] == 0:
                    # v2.6.6: decoy 文件里的 constructor 也要混淆
                    junk_internals.append(f'_zkeep_{jm["ck"]}')
            _add_internal_syms(sym_map, junk_internals, a.seed, 0x7A, items)
        if a.anti_debug:
            adbg_feats_obf = [f.strip() for f in a.adbg_features.split(',') if f.strip()]
            if not adbg_feats_obf:
                adbg_feats_obf = ['frida-agent','libfrida-','gdb-server','libhook','frida']
            adbg_names = ['_a_pst','_a_pmp','_a_fmt','_a_fhk','_a_fr',
                          '_a_noad','_a_dbg','_a_pre',
                          '_a_mhit','_a_mno','_a_mtp','_a_mld','_a_nul',
                          '_a_state','_a_dec','_a_probe']
            for n in ['_a_pst','_a_pmp','_a_fmt','_a_fhk','_a_fr',
                      '_a_noad','_a_dbg','_a_pre',
                      '_a_mhit','_a_mno','_a_mtp','_a_mld','_a_nul']:
                adbg_names.append('_b' + n)
            for idx in range(len(adbg_feats_obf)):
                adbg_names.append(f'_a_ft{idx}')
                adbg_names.append(f'_b_a_ft{idx}')
            _add_internal_syms(sym_map, adbg_names, a.seed, 0x3B, items)
        if file_sigs:
            fnames = []
            for g in file_sigs:
                safe_g = re.sub(r'\W', '_', g)
                fnames.extend([f'_fsig_{safe_g}', f'_fscheck_{safe_g}'])
            _add_internal_syms(sym_map, fnames, a.seed, 0xF5, items)

    ctor_base = a.constructor_base
    default_elf = 'split.so' if a.library else 'split.elf'
    elf_name = obfuscate_names([default_elf], a.seed)[default_elf] \
               if a.obfuscate_target else default_elf

    cflags_extra = ''
    if a.visibility_hidden and not a.library:
        cflags_extra += ' -fvisibility=hidden'
    if a.lto: cflags_extra += ' -flto'
    if a.no_unwind: cflags_extra += ' -fno-asynchronous-unwind-tables -fno-ident'
    ldflags_extra = ''
    if a.strip: ldflags_extra += ' -s'
    if a.lto: ldflags_extra += ' -flto'

    # ---- 打印汇总 ----
    print('== 拆分结果 ==')
    for g in sorted(groups):
        fns = [it.name for it in items if it.group == g and it.kind == 'func_def']
        print(f'  {g:<16} {len(fns):>3} fn  deps={sorted(group_deps.get(g, ()))}')

    if a.obfuscate:
        print('\n== 文件名映射 ==')
        for orig, obf in file_map.items():
            print(f'  {orig:<16} -> {obf}')
    if a.obfuscate_symbols:
        print(f'\n== 符号名混淆 ({len(sym_map)} 个) ==')
        for orig in sorted(sym_map)[:10]:
            print(f'  {orig:<20} -> {sym_map[orig]}')
        if len(sym_map) > 10: print(f'  ... 共 {len(sym_map)} 个')
    if a.obfuscate_target:
        print(f'\n== ELF 名 ==\n  {default_elf} -> {elf_name}')
    if a.encrypt_strings and unique_strings:
        print(f'\n== 字符串加密 ({len(unique_strings)} 个唯一) ==')
        for content, idx in list(unique_strings.items())[:5]:
            enc, key, s = encrypted_data[idx]
            preview = content[:30] + ('...' if len(content) > 30 else '')
            print(f'  DS_{idx:<3} key=0x{key:02x} seed=0x{s:02x}  {preview!r}')
    if a.anti_debug:
        print('\n== Anti-Debug ==\n  3 检测: TracerPid / maps / LD_PRELOAD')
    if a.junk:
        print(f'\n== Junk 校验 ==\n  {len(junk_modules)} 个文件，共 {a.junk_checks} 个校验点，'
              f'失败退出码 0x{a.junk_panic_code:04x}')
        for jm in junk_modules:
            print(f'    {jm["basename"]}.c: {jm["n"]} checks  '
                  f'ck={jm["ck"]}  panic={jm["panic"]}')

    # v2.6.6: dry-run 提前退出
    if a.dry_run:
        print('\n[DRY-RUN] 未生成任何文件')
        sys.exit(0)

    # ---- 清理输出目录 ----
    os.makedirs(a.output, exist_ok=True)
    for f in os.listdir(a.output):
        if f.endswith(('.c','.h','.o','.d','.elf','.so','.json','.txt')) or f == 'Makefile':
            try: os.remove(os.path.join(a.output, f))
            except OSError: pass

    decrypt_h_name = file_map.get('decrypt.h') if (a.encrypt_strings and unique_strings) else None
    adbg_h_name    = file_map.get('adbg.h') if a.anti_debug else None
    junk_h_names = [file_map[f'{jm["basename"]}.h'] for jm in junk_modules] \
                   if a.junk else None

    gen_common_h(items, a.output, file_map['common.h'], sym_map,
                 decrypt_h_name, adbg_h_name, junk_h_names)
    if has_common_defs:
        gen_common_c(items, a.output, file_map['common.c'],
                     file_map['common.h'], sym_map, global_arrays, file_sigs,
                     ctor_base=ctor_base)
    for g in groups:
        if g == a.common: continue
        gen_group_h(g, items, group_deps, a.output,
                    file_map[f'{g}.h'], file_map, sym_map)
        gen_group_c(g, items, a.output, file_map[f'{g}.c'],
                    file_map[f'{g}.h'], sym_map, global_arrays, file_sigs,
                    ctor_base=ctor_base)

    if a.encrypt_strings and unique_strings:
        gen_decrypt_h(a.output, file_map['decrypt.h'], len(unique_strings),
                      sym_map=sym_map)
        gen_decrypt_c(a.output, file_map['decrypt.c'],
                      unique_strings, encrypted_data, krot,
                      sym_map=sym_map, seed=a.seed)
        kp = dump_keys(a.output, krot, unique_strings, encrypted_data, a.seed)
        print(f'  密钥已保存: {kp}')
    if a.anti_debug:
        adbg_feats_call = [f.strip() for f in a.adbg_features.split(',') if f.strip()]
        if not adbg_feats_call:
            adbg_feats_call = ['frida-agent','libfrida-','gdb-server','libhook','frida']
        gen_antidebug_h(a.output, file_map['adbg.h'], sym_map=sym_map)
        gen_antidebug_c(a.output, file_map['adbg.c'], sym_map=sym_map,
                        features=adbg_feats_call,
                        adbg_priority=a.adbg_priority)
    if a.junk:
        for jm in junk_modules:
            gen_junk_h(a.output, file_map[f'{jm["basename"]}.h'],
                       jm['ck'], jm['panic'], sym_map=sym_map,
                       basename=jm['basename'])
            gen_junk_c(a.output, file_map[f'{jm["basename"]}.c'],
                       jm['n'], jm['seed'], jm['table'], jm['expected'],
                       jm['panic_code'], jm['ck'], jm['panic'],
                       sym_map=sym_map, ctor_base=ctor_base)

    ldflags = a.ldflags or detect_ldflags(items)
    src_dir = os.path.dirname(os.path.abspath(a.input))
    src_dir_rel = os.path.relpath(src_dir, os.path.abspath(a.output))
    if a.library:
        gen_makefile_lib(a.output, ldflags, elf_name, cflags_extra, ldflags_extra,
                         src_dir_rel=src_dir_rel)
    else:
        gen_makefile(a.output, ldflags, elf_name, cflags_extra, ldflags_extra,
                     src_dir_rel=src_dir_rel)
    if a.standalone and not a.library:
        gen_standalone(a.output, groups, group_deps, ldflags,
                       file_map, sym_map, elf_name)

    if a.obfuscate or a.obfuscate_target:
        fm = dict(file_map)
        if a.obfuscate_target: fm['__elf__'] = elf_name
        with open(os.path.join(a.output, 'file_map.json'), 'w') as f:
            json.dump(fm, f, indent=2, ensure_ascii=False)
    if a.obfuscate_symbols:
        with open(os.path.join(a.output, 'symbol_map.json'), 'w') as f:
            json.dump(sym_map, f, indent=2, ensure_ascii=False)

    out_files = sorted(f for f in os.listdir(a.output)
                       if f.endswith(('.c', '.so', '.elf')))
    print(f'\n✓ 输出目录: {a.output}/')
    print(f'  .c 文件: {", ".join(f for f in out_files if f.endswith(".c"))}')
    print(f'  {"LIB" if a.library else "ELF"}:     {elf_name}')
    print(f'  链接库:  {ldflags or "(无)"}')
    print(f'  CFLAGS:  -O2 -Wall -I.{cflags_extra or " (无额外)"}')
    print(f'  LDFLAGS: {ldflags}{ldflags_extra or ""}')

    if a.verify:
        ok = verify(a.input, a.output, a.cc, a.cflags, a.ldflags, elf_name,
                    cflags_extra, ldflags_extra, library=a.library)
        sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()