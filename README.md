# Arkari
Yet another llvm based obfuscator based on [goron](https://github.com/amimo/goron).

当前支持特性：
 - 混淆过程间相关
 - 间接跳转,并加密跳转目标(`-mllvm -irobf-indbr`)
 - 间接函数调用,并加密目标函数地址(`-mllvm -irobf-icall`)
 - 间接全局变量引用,并加密变量地址(`-mllvm -irobf-indgv`)
 - 字符串(c string)加密功能(`-mllvm -irobf-cse`)
 - 过程相关控制流平坦混淆(`-mllvm -irobf-cff`)
 - 整数常量加密(`-mllvm -irobf-cie`) (Win64-MT-19.1.3-obf1.6.0 or later)
 - 浮点常量加密(`-mllvm -irobf-cfe`) (Win64-MT-19.1.3-obf1.6.0 or later)
 - 全部 (`-mllvm -irobf-indbr -mllvm -irobf-icall -mllvm -irobf-indgv -mllvm -irobf-cse -mllvm -irobf-cff -mllvm -irobf-cie -mllvm -irobf-cfe`)

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

## Acknowledgements

Thanks to [JetBrains](https://www.jetbrains.com/?from=KomiMoe) for providing free licenses such as [Resharper C++](https://www.jetbrains.com/resharper-cpp/?from=KomiMoe) for my open-source projects.

[<img src="https://resources.jetbrains.com/storage/products/company/brand/logos/ReSharperCPP_icon.png" alt="ReSharper C++ logo." width=200>](https://www.jetbrains.com/resharper-cpp/?from=KomiMoe)

## 参考资源

+ [Goron](https://github.com/amimo/goron)
+ [Hikari](https://github.com/HikariObfuscator/Hikari)
+ [ollvm](https://github.com/obfuscator-llvm/obfuscator)
