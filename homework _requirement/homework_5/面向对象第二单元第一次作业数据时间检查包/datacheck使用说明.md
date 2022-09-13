## Datacheck1程序使用说明

#### 程序功能

本 `datacheck1` 程序基于ALS调度策略度量给定第二单元第一次作业的输入的电梯运行时间。

#### 使用说明

1. 请将包含输入的文件以`stdin.txt`命名，放置在相同路径下。

2. 在命令行中执行二进制文件。

   例：

   ```bash
   #linux
   chmod u+x datacheck1_linux
   ./datacheck1_linux
   #windows
   ./datacheck1.exe
   #mac
   ./datacheck1_mac
   ```

   对于合法输入，程序将输出$T_{base}$和$T_{max}$。程序**不提供处理错误数据的能力**

提示：请根据操作系统使用对应的二进制文件。

