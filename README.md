
<h1 align="center">Arkari</h1>
<p align="center">
 <a href="https://discord.gg/f5nDYjsrKZ">
  <img width="180" src="https://discordapp.com/api/guilds/1391744742148145294/widget.png" />
 </a>
</p>
<p align="center">
 <a href="https://github.com/KomiMoe/Arkari/issues">
  <img src="https://img.shields.io/github/issues/KomiMoe/Arkari"/> 
 </a>
 <a href="https://github.com/KomiMoe/Arkari/network/members">
  <img src="https://img.shields.io/github/forks/KomiMoe/Arkari"/> 
 </a>  
 <a href="https://github.com/KomiMoe/Arkari/stargazers">
  <img src="https://img.shields.io/github/stars/KomiMoe/Arkari"/> 
 </a>
 <a href="https://github.com/KomiMoe/Arkari/LICENSE">
  <img src="https://img.shields.io/github/license/KomiMoe/Arkari?"/> 
 </a>
</p>
<p align="center">
 <a helf="https://github.com/KomiMoe/Arkari/releases">
  <img alt="GitHub Downloads (all assets, all releases)" src="https://img.shields.io/github/downloads/KomiMoe/Arkari/total">
 </a>
 <a helf="https://github.com/KomiMoe/Arkari/releases">
  <img alt="GitHub Release" src="https://img.shields.io/github/v/release/KomiMoe/Arkari">
 </a>
</p>
<h3 align="center">Yet another llvm based obfuscator based on goron</h3>

## 介绍
当前支持特性：
 - 混淆过程间相关
 - 间接跳转,并加密跳转目标(`-mllvm -irobf-indbr`)
 - 间接函数调用,并加密目标函数地址(`-mllvm -irobf-icall`)
 - 间接全局变量引用,并加密变量地址(`-mllvm -irobf-indgv`)
 - 字符串(c string)加密功能(`-mllvm -irobf-cse`)
 - 过程相关控制流平坦混淆(`-mllvm -irobf-cff`)
 - 整数常量加密(`-mllvm -irobf-cie`) (Win64-MT-19.1.3-obf1.6.0 or later)
 - 浮点常量加密(`-mllvm -irobf-cfe`) (Win64-MT-19.1.3-obf1.6.0 or later)
 - Microsoft CXXABI RTTI Name 擦除器 (实验性功能!) [需要指定配置文件路径 以及 配置文件`randomSeed`字段(32字节，不足会在后面补0，超过会截断)] (`-mllvm -irobf-rtti`) (Win64-MT-20.1.7-obf1.7.0 or later)
 - 全部 (`-mllvm -irobf-indbr -mllvm -irobf-icall -mllvm -irobf-indgv -mllvm -irobf-cse -mllvm -irobf-cff -mllvm -irobf-cie -mllvm -irobf-cfe -mllvm -irobf-rtti`)
 - 或直接通过配置文件管理(`-mllvm -arkari-cfg="配置文件路径|Your config path"`) (Win64-MT-20.1.7-obf1.7.0 or later)

对比于goron的改进：
 - 由于作者明确表示暂时(至少几万年吧)不会跟进llvm版本和不会继续更新. 所以有了这个版本(https://github.com/amimo/goron/issues/29)
 - 更新了llvm版本
 - 编译时输出文件名, 防止憋死强迫症
 - 修复了亿点点已知的bug
 ```
 - 修复了混淆后SEH爆炸的问题
 - 修复了dll导入的全局变量会被混淆导致丢失__impl前缀的问题
 - 修复了某些情况下配合llvm2019(2022)插件会导致参数重复添加无法编译的问题
 - 修复了x86间接调用炸堆栈的问题
 - ...
 ```
## 编译

 - Windows(use Ninja, Ninja YYDS):
```
install ninja in your PATH
run x64(86) Native Tools Command Prompt for VS 2022(xx)
run:

mkdir build_ninja
cd build_ninja
cmake -DCMAKE_CXX_FLAGS="/utf-8" -DCMAKE_INSTALL_PREFIX="./install" -DCMAKE_MSVC_RUNTIME_LIBRARY=MultiThreaded -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_PROJECTS="clang;lld;lldb" -G "Ninja" ../llvm
ninja
ninja install

```

 - Windows with cmake for using clang(use Ninja, With vcpkg for libxml2 libLZMA, zlib ):
```
install ninja in your PATH
run x64 Native Tools Command Prompt for VS 2022
run:

vcpkg install zlib:x64-windows-static
vcpkg install libLZMA:x64-windows-static
vcpkg install libxml2:x64-windows-static

mkdir build_ninja
cd build_ninja

Replace "YOUR_VCPKG_TOOLCHAIN_FILE" to your vcpkg toolchain file (You can query it for command "vcpkg integrate install"):
cmake -DCMAKE_CXX_FLAGS="/utf-8" -DCMAKE_INSTALL_PREFIX="./install" -DCMAKE_MSVC_RUNTIME_LIBRARY=MultiThreaded -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_PROJECTS="clang;lld;lldb" -DLLVM_BUILD_TOOLS=ON -DLLVM_ENABLE_LIBXML2=ON -DCMAKE_TOOLCHAIN_FILE=YOUR_VCPKG_TOOLCHAIN_FILE -DVCPKG_TARGET_TRIPLET="x64-windows-static" -G "Ninja" ../llvm

ninja
ninja install

```

## 使用
可通过编译选项开启相应混淆，如启用间接跳转混淆：

```
$ path_to_the/build/bin/clang -mllvm -irobf -mllvm --irobf-indbr test.c
```
对于使用autotools的工程：
```
$ CC=path_to_the/build/bin/clang or CXX=path_to_the/build/bin/clang
$ CFLAGS+="-mllvm -irobf -mllvm --irobf-indbr" or CXXFLAGS+="-mllvm -irobf -mllvm --irobf-indbr" (or any other obfuscation-related flags)
$ ./configure
$ make
```
对于使用VisualStudio的项目，可以使用VisualStudio插件： https://github.com/KomiMoe/llvm2019


## 可以通过**annotate**对特定函数**开启/关闭**指定混淆选项：
(Win64-19.1.0-rc3-obf1.5.0-rc2 or later)

annotate的优先级**永远高于**命令行参数

`+flag` 表示在当前函数启用某功能, `-flag` 表示在当前函数禁用某功能

字符串加密基于LLVM Module，所以必须在编译选项中加入字符串加密选项，否则不会开启

可用的annotate  flag:
- `fla`
- `icall`
- `indbr`
- `indgv`
- `cie`
- `cfe`

```cpp
//fla表示编译选项中的cff

[[clang::annotate("-fla -icall")]]
int foo(auto a, auto b) {
    return a + b;
}

[[clang::annotate("+indbr +icall")]]
int main(int argc, char** argv) {
    foo(1, 2);
    std::printf("hello clang\n");
    return 0;
}
// 当然如果你不嫌麻烦也可以用 __attribute((__annotate__(("+indbr"))))
```

如果你不希望对整个程序都启用Pass，那么你可以在编译命令行参数中只添加 `-mllvm -irobf` ，然后使用 **annotate** 控制需要混淆的函数，仅开启 **-irobf** 不使用 **annotate** 不会运行任何混淆Pass

当然，不添加任何混淆命令行参数的情况下，仅使用 **annotate** 也***不会***启用任何Pass

你**不能**同时开启和关闭某个混淆参数！
当然以下情况会报错：

```cpp
[[clang::annotate("-fla +fla")]]
int fool(auto a, auto b){
    return a + b;
}
```



## 可以使用下列几种方法之一单独控制某个混淆Pass的强度
(Win64-19.1.0-rc3-obf1.5.1-rc5 or later)

如果不指定强度则默认强度为0，annotate的优先级永远高于命令行参数

可用的Pass:
- `icall` (强度范围: 0-3)
- `indbr` (强度范围: 0-3)
- `indgv` (强度范围: 0-3)
- `cie` (强度范围: 0-3)
- `cfe` (强度范围: 0-3)

1.通过**annotate**对特定函数指定混淆强度：

 `^flag=1` 表示当前函数设置某功能强度等级(此处为1)
 
```cpp
//^icall=表示指定icall的强度
//+icall表示当前函数启用icall混淆, 如果你在命令行中启用了icall则无需添加+icall

[[clang::annotate("+icall ^icall=3")]]
int main() {
    std::cout << "HelloWorld" << std::endl;
    return 0;
}
```

2.通过命令行参数指定特定混淆Pass的强度

Eg.间接函数调用,并加密目标函数地址,强度设置为3(`-mllvm -irobf-icall -mllvm -level-icall=3`)


## 通过配置文件管理混淆参数
(Win64-MT-20.1.7-obf1.7.0 or later)

编译参数加上：`-mllvm -arkari-cfg="配置文件路径|Your config path"` 

路径可以是绝对路径，或者相对于编译器工作目录的相对路径

配置文件格式为json

Eg :
```json
{
  "randomSeed": "zX0^bS5|vP0@xO4+sF3[pX8,fG2^rT9?",
  "indbr": {
    "enable": true,
    "level": 3
  },
  "icall": {
    "enable": true,
    "level": 3
  },
  "indgv": {
    "enable": true,
    "level": 3
  },
  "cie": {
    "enable": true,
    "level": 3
  },
  "cfe": {
    "enable": true,
    "level": 3
  },
  "fla": {
    "enable": true
  },
  "cse": {
    "enable": true
  },
  "rtti": {
    "enable": true
  }
}

```

## Acknowledgements

Thanks to [JetBrains](https://www.jetbrains.com/?from=KomiMoe) for providing free licenses such as [Resharper C++](https://www.jetbrains.com/resharper-cpp/?from=KomiMoe) for my open-source projects.

[<img src="https://resources.jetbrains.com/storage/products/company/brand/logos/ReSharperCPP_icon.png" alt="ReSharper C++ logo." width=200>](https://www.jetbrains.com/resharper-cpp/?from=KomiMoe)



## Star History

<a href="https://www.star-history.com/#KomiMoe/Arkari&Date">
 <picture>
   <source media="(prefers-color-scheme: dark)" srcset="https://api.star-history.com/svg?repos=KomiMoe/Arkari&type=Date&theme=dark" />
   <source media="(prefers-color-scheme: light)" srcset="https://api.star-history.com/svg?repos=KomiMoe/Arkari&type=Date" />
   <img alt="Star History Chart" src="https://api.star-history.com/svg?repos=KomiMoe/Arkari&type=Date" />
 </picture>
</a>

## 参考资源

+ [Goron](https://github.com/amimo/goron)
+ [Hikari](https://github.com/HikariObfuscator/Hikari)
+ [ollvm](https://github.com/obfuscator-llvm/obfuscator)
