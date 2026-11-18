# CSplitGuard – C 源码拆分混淆工具

## 简介

`csplit.py` 是一个 C 语言源代码自动拆分与混淆保护工具。它将单个 C 源文件拆分为多个模块，并对每个模块施加字符串加密、反调试、虚假校验、符号混淆、文件完整性签名等多层保护，最终编译为单一 ELF 可执行文件。

## 环境要求

- Python 3.6+
- GCC（用于编译验证，可选但推荐）
- Linux / macOS（Windows 可通过 WSL 或 MinGW 使用）

## 安装

无需安装，直接下载 `csplit.py` 即可运行：

```bash
git clone https://github.com/yourusername/csplitguard.git
cd csplitguard
chmod +x csplit.py
```
```bash
python3 csplit.py <input.c> [options]
```

### 必需参数

| 参数 | 说明 |
|------|------|
| `<input.c>` | 要拆分和混淆的 C 源文件 |

### 选项

| 选项 | 说明 |
|------|------|
| `-o, --output-dir DIR` | 输出目录（默认 `./output`） |
| `--prefix PREFIX` | 生成文件的前缀（默认 `mod`） |
| `--map FILE` | 指定 JSON 映射文件，用于自定义分组和导出符号 |
| `--no-obfuscate` | 禁用标识符混淆 |
| `--no-encrypt` | 禁用字符串加密 |
| `--no-anti-debug` | 禁用反调试代码注入 |
| `--junk-checks NUM` | 插入 NUM 个虚假校验点（默认 0） |
| `--junk-files NUM` | 创建 NUM 个虚假源文件（默认 0） |
| `--panic-code HEX` | 校验失败时的退出码（十六进制，默认 `0xDEAD`） |
| `--verify` | 编译验证：自动编译输出目录并测试运行 |
| `--standalone` | 生成独立的测试可执行文件（与 `--verify` 配合） |
| `--library` | 生成共享库（`.so`）而非可执行文件 |
| `--keep-temp` | 保留中间文件（`.o` 等） |
| `-h, --help` | 显示帮助信息 |

### 示例

```bash
# 基本拆分+默认混淆
python3 csplit.py myapp.c -o ./protected

# 高安全模式
python3 csplit.py myapp.c --junk-checks 50 --junk-files 20 --panic-code 0xBEEF

# 编译验证并生成独立测试程序
python3 csplit.py myapp.c --verify --standalone

# 使用自定义分组映射
python3 csplit.py myapp.c --map group_map.json

# 生成共享库
python3 csplit.py mylib.c --library
```
