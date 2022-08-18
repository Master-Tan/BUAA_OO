## 面向对象设计与构造预习作业3-4

### 第一部分：训练目标

本次作业是针对正则表达式中模糊匹配和非贪婪匹配模式的练习，藉此同学们可以了解不同匹配模式的效果和性能差异。

----

### 第二部分：题目背景

有些用户喜欢在群聊或聊天中使用昵称，比如名为 “小枫”的用户可以有昵称 “小小枫”、“小枫枫”。

用户名或备注的前缀或后缀可能含有一些特殊含义，比如“2006 张一一”、“2006 刘一一”、“王一一 19级”、“陈一一 20级”，其中的数字代表着年，隐含着当年入学或入职等信息。

----

### 第三部分：题目描述

群聊消息可能被表现成以下三种模式：

- 给个人的消息：

  ``` 
  2021/07/12-student@teacher :"can i pass the exam?";
  ```

  本消息为发送给个人的消息，指定了接收者teacher。

- 群聊中的消息，指定了接收者：

  ``` 
  2021/07/12-student:"can i pass the exam?@teacher ";
  ```
  
  本消息为在群聊中发送的消息，指定了接收者teacher。

- 群聊中的消息，未指定接收者：

  ``` 
  2021/07/12-student:"can i pass the exam?";
  ```
  
  本消息为在群聊中发送的消息，未指定接收者。

请编写程序读入消息，并根据输入的查询找出指定了接收者并且该接收者的用户名包含指定前缀、后缀、子串或子序列的消息。

----

### 第四部分：输入/输出说明


#### 输入格式

我们递归地定义：

- **a(x)**： 表示连续的 x 个 a, 如 a(3) = aaa
- **ab(x)** ：表示连续的 x 个 ab，如 ab(3) = ababab
- **+**：表示字符串的拼接，aa + bb = aabb
- **子序列**：将字符串中零个或多个字符去掉后所得结果，一个字符串 abc 的子序列有 a, b, c, ab, ac, bc, abc
- **子串**：字符串中任意个连续的字符组成的子序列
- **A类串**：符合a(x)+b(y)+c(z)所描述的字符串，所含字符的数量较小
  - 其中x∈[2, 3], y∈[2, 4], z∈[2, 4]
  - 例如 aabbcc、aabbccc、aabbcccc、aabbbcc、aabbbbcc、aabbbccc、aabbbccc、aabbbbccc、aabbbbcccc均是符合要求的串
- **B类串**：符合a(x)+b(y)+c(z)所描述的字符串，所含字符的数量较大
  - 其中x∈[2, 3], y∈[2, 1000000], z∈[2, 4]
  - 例如 aabbccc是一个符合要求的串

前若干行为消息内容，以一行END_OF_MESSAGE结尾。

其后为多条查询语句，每行一条。

每条查询语句的格式为`qmess 参数1 参数2`，**每条查询语句的返回结果是$n$行消息，$n\in[0,+\infin)$**，其中参数的解释如下：

参数1为字母A或B，表示所询问的是A类串还是B类串；

参数2是一个值在1到4之间的整数，其描述了我们期望该查询语句所返回的消息的集合中，每条消息的**消息内容**应当以何种方式来包含参数1所指定的特定类型字符串。具体规定如下表所示:

| 参数2取值 | 消息内容以何种方式包含[参数1]类型的字符串 |
| --------- | ----------------------------------------- |
| 1         | 消息内容中以[参数1]类型的字符串为前缀     |
| 2         | 消息内容中以[参数1]类型的字符串为后缀     |
| 3         | 消息内容中以[参数1]类型的字符串为子串     |
| 4         | 消息内容中以[参数1]类型的字符串为子序列   |

具体的例子请参见[样例部分](#输入样例)。

#### 输出格式

对于每一条询问，输出指定消息（输入数据中可能存在多条消息符合条件，此时按照**原顺序、原格式**输出全部符合条件的消息）。

输出中每条消息均单独占据一行。

#### 输入样例
<a name="输入样例"></a>

```
2021/7/1-Jack@JayChou :"Hello! mydear aabbcc.";2021/7/3-JayChou@buaaer :"aabbcccc, nice to meet you.";
2021/7/5-JayChou@Mike :"emmmm...aabbbcc, I'm sorry.";
2021/7/6-JayChou@Mike :"emmmm...aabbbbbbbcc, I don't want to talk to you.";         2020/7/8-JayChou@buaaer :"Hahaha! see you again abc";
2020/7/8-JayChou@Sabbaty :"Hahaha! Sabbaty, come to the center!";
2021/6/8-JayChou:"I'm aaabbbbbbbbcc!";
2021/7/11-JayChou:"aaabbbbbbbbcc, I love you!";
2021/1/1-JayChou:"aabbc@c ";
END_OF_MESSAGE
qmess A 1
qmess A 2
qmess A 3
qmess A 4
qmess B 1
qmess B 2
qmess B 3
qmess B 4
```

#### 输出样例

```
2021/7/3-JayChou@buaaer :"aabbcccc, nice to meet you.";
2021/7/1-Jack@JayChou :"Hello! mydear aabbcc.";
2021/7/3-JayChou@buaaer :"aabbcccc, nice to meet you.";
2021/7/5-JayChou@Mike :"emmmm...aabbbcc, I'm sorry.";
2021/7/1-Jack@JayChou :"Hello! mydear aabbcc.";
2021/7/3-JayChou@buaaer :"aabbcccc, nice to meet you.";
2021/7/5-JayChou@Mike :"emmmm...aabbbcc, I'm sorry.";
2021/7/6-JayChou@Mike :"emmmm...aabbbbbbbcc, I don't want to talk to you.";
2020/7/8-JayChou@Sabbaty :"Hahaha! Sabbaty, come to the center!";
2021/6/8-JayChou:"I'm aaabbbbbbbbcc!";
2021/7/11-JayChou:"aaabbbbbbbbcc, I love you!";
2021/1/1-JayChou:"aabbc@c ";
2021/7/3-JayChou@buaaer :"aabbcccc, nice to meet you.";
2021/7/11-JayChou:"aaabbbbbbbbcc, I love you!";
2021/7/1-Jack@JayChou :"Hello! mydear aabbcc.";
2021/7/3-JayChou@buaaer :"aabbcccc, nice to meet you.";
2021/7/5-JayChou@Mike :"emmmm...aabbbcc, I'm sorry.";
2021/7/6-JayChou@Mike :"emmmm...aabbbbbbbcc, I don't want to talk to you.";
2021/6/8-JayChou:"I'm aaabbbbbbbbcc!";
2021/7/11-JayChou:"aaabbbbbbbbcc, I love you!";
2021/7/1-Jack@JayChou :"Hello! mydear aabbcc.";
2021/7/3-JayChou@buaaer :"aabbcccc, nice to meet you.";
2021/7/5-JayChou@Mike :"emmmm...aabbbcc, I'm sorry.";
2021/7/6-JayChou@Mike :"emmmm...aabbbbbbbcc, I don't want to talk to you.";
2020/7/8-JayChou@Sabbaty :"Hahaha! Sabbaty, come to the center!";
2021/6/8-JayChou:"I'm aaabbbbbbbbcc!";
2021/7/11-JayChou:"aaabbbbbbbbcc, I love you!";
2021/1/1-JayChou:"aabbc@c ";
```

#### 样例解释

```
2020/7/8-JayChou@Sabbaty :"Hahaha! Sabbaty, come to the center!";
```

该信息中Hahaha中有子序列aaa，Sabbaty中有子序列bb，come to the center中有子序列cc。因此是含有子序列aaabbcc，也可以说是含有子序列aabbcc。

```
2021/1/1-JayChou:"aabbc@c ";
```

该信息中含有`aabbcc`的子序列

####  数据限制

- 日期仅以 **year/month/day** 形式给出，$year \isin [0, 9999], mounth \isin [1, 12], day \isin [0,31]$。日期中可能存在前导`0`，比如`1`月可以表示为`01`月，`258`年可以表示为`0258`年。

- 发送者和接收者的用户名仅由**大小写英文字母、数字**组成。

- 正文内容仅由**大小写英文字母、数字、空格、四种标点符号（? ! , .）构成**。

- 输入数据中所有内容均对大小写**敏感**。

- 如果一条消息中存在@用户的情况（对应前两种消息模式），则保证该信息中`@+用户名`结构后面一定**有一个空格**。

- 日期、用户名、正文都非空。
- 不超过300行
- 每行不超过10个消息
- 总询问数不超过100条

----

### 第五部分：提示

- 关于模糊匹配和非贪婪匹配模式：对于表达式中间可能出现的无关紧要的部分，我们通常采用模糊匹配来进行处理。同时，由于性能原因，我们建议大家使用**非贪婪模式**进行匹配。

  我们通常使用`.*?`来表示非贪婪模式，其中`.`表示任意字符，`*?`表示重复任意次，但尽可能少重复。顾名思义，非贪婪模式就是在能使整个匹配成功的前提下匹配最少的字符，比如如果将`a.*?b`应用在`aabab`中，我们匹配到的会是`aab`
  
- 关于非贪婪匹配模式还有一些其他表示方式可供参考：

| 代码   | 说明                            |
| ------ | ------------------------------- |
| *？    | 重复任意次，但尽可能少重复      |
| +？    | 重复1次或更多次，但尽可能少重复 |
| ？？   | 重复0次或1次，但尽可能少重复    |
| {n,m}? | 重复n到m次，但尽可能少重复      |
| {n,}?  | 重复n次以上，但尽可能少重复     |

相关详细内容可以参考
  https://www.runoob.com/java/java-regular-expressions.html
  https://www.jb51.net/article/183106.htm

  