##  面向对象设计与构造预习作业3-1

> pre3主要训练字符串的处理能力，以及正则表达式相关知识。本单元作业同样是以 Task 的演进方式进行迭代，我们直接给了同学们从 Task1 ~ Task5 的所有题面，**希望同学们在动笔之前先完整阅读一遍指导书，**从Task1 开始顺序做题，并在做题的同时思考如何给后续的迭代留下修改的空间，而不至于每一个新的 Task 都要重新写一份代码。。

### 第一部分：训练目标

本次作业的主要目标是学习使用结构化方式来对字符串进行处理，以识别和提取其中的结构化信息。

----

### 第二部分：题目背景

小明在一门课的大作业中设计和实现了一款聊天软件，本单元作业围绕这个小型聊天系统展开。该系统中聊天消息的格式为：

```
日期-发送者@接收者[此处有一个空格]:"正文";
```

例如：

```
2021/07/12-student@teacher :"can i pass the exam?";
```

这是2021年7月12日，student给teacher的一条消息，消息内容为"can i pass the exam?"。所有消息以分号（;）结束。

----

### 第三部分：题目描述

数据包含多行，每行有一条或多条消息。用**分号**或**分号+若干空格**间隔开来。

请编写程序，对输入的数据进行解析，并输出所有消息。

### 第四部分：输入/输出格式

#### 输入格式

多行数据，每行有一条或多条消息，用**分号**或**分号+若干空格**间隔开来。

#### 输出格式

输出所有接收到的消息，其中每条消息均单独占据一行。

#### 样例输入

```
2021/7/1-Jack@JayChou :"Hello!";2021/7/3-JayChou@buaaer :"Hahaha";
2021/7/5-JayChou@Mike :"emmmm";         2021/7/8-JayChou@buaaer :"Hahaha";
```

#### 样例输出

```
2021/7/1-Jack@JayChou :"Hello!";
2021/7/3-JayChou@buaaer :"Hahaha";
2021/7/5-JayChou@Mike :"emmmm";
2021/7/8-JayChou@buaaer :"Hahaha";
```

#### 数据限制

- 日期仅以 **year/month/day** 形式给出，$year \isin [0, 9999], month \isin [1, 12], day \isin [0,31]$。日期中可能存在前导`0`，比如`1`月可以表示为`01`月，`258`年可以表示为`0258`年。

- 发送者和接收者的用户名仅由**大小写英文字母、数字**组成。

- 正文内容仅由**大小写英文字母、数字、空格、四种标点符号（? ! , .）构成**。

- 输入数据中所有内容均对大小写**敏感**。

- 日期、用户名、正文都非空。
- 输入不超过300行
- 输入的每行数据不超过10个消息

### 第五部分：提示与说明

Java类库中的String类提供了很多可以帮助你完成这几个Task的辅助方法。例如：
- split方法，可以根据给定的分隔符来将字符串分割为若干个字符串；
- indexOf方法，可以在给定的字符串中搜索给定字符串出现的位置；
- substring方法，可以按照下表位置区间来从给定字符串截取子字符串;
- trim方法，可以移除给定字符串开头和结尾处的空格以及换行符。
  **请注意：**在各主流IDE中，你可以通过将鼠标悬停在方法名上来阅读方法的文档。这可以让你精确地了解该方法的具体作用，• 为熟悉java类库的使用提供很大的帮助。

下面以一个简单的例子来辅助说明以上所提及的各个方法。

假设我们已经得到了含有如下信息的字符串：
```json
{
"code":"iVBORw@0KGgoAAAANSU#hEUgAAAAgAAA$AECAYAAACzzX7wAAAAGUlEQVQImW%NggID/DKjgPzYOLpqwAr^xWAAAbkwv1&EmB71QAAAABJRU5*ErkJggg==",
"key":"64",
"type":"png"
}
```
现在我们想要将其中的code部分提取出来进行进一步的处理。

我们可以通过字符串查找的方式来完成该任务：

```java
public static String extractCode(String jsonString) {
    int start = jsonString.indexOf("\"code\"");           //找到"code"所在之处；
    int end = jsonString.indexOf("\n", start);            //从上一次搜索结果开始向后搜索换行符
    return jsonString.substring(start + 8, end - 2);      //根据以上信息截取子串并返回
}
```

当然，这种方法并没有对字符串进行实际的解析，仅仅是进行了提取。

我们也可以利用split方法来完成这一任务：

```java
public static String extractCode(String jsonString) {
    String[] records = jsonString.substring(1, jsonString.length() - 1).split(","); //将输入的字符串按照逗号分割开
    for (String record : records) {
        String[] details = record.split(":");                                       //分离每个分割出的字符串中的名称与值（按照冒号进一步分割）
        if ("\"code\"".equals(details[0])) {                                        //判断数据名称是否为"code"
            return details[1].substring(1, details[1].length() - 1);                //返回该数据对应的值。
        }
    }
    throw new RuntimeException("keyword code not found!");                          //未找到，报错
}
```

当然，你也可以选择功能更为强大的*正则表达式*来完成本任务。该方法将在下一个task中介绍。

