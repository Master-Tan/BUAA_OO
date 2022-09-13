## 面向对象设计与构造第十五次作业

**写在前面：请勿提交官方包代码，仅提交自己实现的类。更不要将官方包的 JML 或代码粘贴到自己的类中，否则以作弊、抄袭论处。**

### 第一部分：训练目标

扩展 UML 解析器，使其支持对 UML 类图、状态图和顺序图的分析，可以通过输入相应的指令来进行相关查询，并能根据 UML 规则进行一定的规范性验证。

---

### 第二部分：预备知识

同学们需要掌握 UML 图的相关知识，以及 [StarUML](http://staruml.io/) 的使用方法。在这里给出一些相关参考资料：

- [第四单元手册](http://gitlab.oo.buaa.edu.cn/2022_public/training/unit-4/training-4/-/blob/main/%E7%AC%AC%E5%9B%9B%E5%8D%95%E5%85%83%E6%89%8B%E5%86%8C.pdf)

---

### 第三部分：基本概念

> 除了如下改动：
>
> - 增加**_某字段为空_**的定义
>
> 其余部分内容与上次作业完全相同。

此处给出一些后文中将会用到的定义。所有用到的定义都会用**_加粗倾斜体_**标注。

如果有需要，你可以在后文遇到**_加粗倾斜体_**的定义时，再回来查阅对应的概念说明。

#### 传入参数与返回值

UML 中操作参数元素 `UMLParameter` 的 `direction` 属性决定了它是传入参数还是返回值：

- `in`：传入参数
- `return`：返回值

在所有的数据中，`direction` 只会有上述两种类型。

#### NamedType

对于属性和操作中的传入参数而言，`NamedType` 包括

- Java 语言的八大基本类型（`byte`/`short`/`int`/`long`/`float`/`double`/`char`/`boolean`）
- `String`

其余一律视为错误类型。

对于操作中的返回值而言，`NamedType` 包括

- Java 语言的八大基本类型（`byte`/`short`/`int`/`long`/`float`/`double`/`char`/`boolean`）
- `String`
- `void`（实际上，`void` 也算是一种类型，C/C++/Java 对于这件事也都是这样的定义，`void` 不等同于无返回值）

其余一律视为错误类型。

#### ReferenceType

对于属性和操作中的传入参数、返回值而言，`ReferenceType` 指向已定义的**类**或**接口**，类型名为对应的**类名**或**接口名**。在本单元中，我们保证它是合法的，即 `ReferenceType` 不可能为错误类型。

#### 类型相同

当两个类型对应的 `NameableType` 对象（参见官方包中的相关接口）在 `Objects.equals()` 下为真时，则这两个类型相同。

#### 参数列表相同

对于任意两个操作，若它们具有相同数量的**传入参数**，且这两组传入参数之间存在某**一一映射**使得相对应的参数**_类型相同_**，则这两个操作的参数列表相同。例如 `int op(int, Class1, double)` 和 `String op(double, int, Class1)` 的参数列表相同。

#### 重复操作

对于任意两个操作，如果它们的**名称相同**，且操作的**_参数列表相同_**，则它们互为重复操作。

#### 耦合度

OO 度量指标中的类耦合度（Coupling Between Objects, CBO）最早由 Chidamber 与 Kemerer 于 1994 年提出，并被后人不断完善。在这里，我们采用 Visual Studio 2019 中 [类耦合度指标](https://docs.microsoft.com/en-us/visualstudio/code-quality/code-metrics-class-coupling?view=vs-2019#ck94) 的约定，给出本单元中操作的耦合度与属性的耦合度的相关计算规则。

**操作的耦合度**：对于一个类的某个操作，考虑其所有类型为 `ReferenceType` 的操作参数类型（即元素 `UMLParameter` 的 `type` 属性，包括传入参数与返回值）：

- 若 `ReferenceType` 引用的类或接口是当前查询的类，则耦合度不增加，否则耦合度增加 $1$；
- 若存在多个 `ReferenceType` 引用的类或接口相同，则耦合度只会被计算一次，不会重复计算。

**属性的耦合度**：对于一个类，考虑其所有类型为 `ReferenceType` 的属性类型（即元素 `UMLAttribute` 的 `type` 属性）：

- 若 `ReferenceType` 引用的类或接口是当前查询的类，则耦合度不增加，否则耦合度增加 $1$；
- 若存在多个 `ReferenceType` 引用的类或接口相同，则耦合度只会被计算一次，不会重复计算。

#### 继承深度

对于类 X，若 Y 满足：

- X 是 Y 的子类（此处特别定义，X 也是 X 的子类）；
- 不存在类 Z，使得 Z 是 Y 的父类；

则称 Y 是 X 的顶级父类。这里的继承关系只考虑 UML 中存在的 `UmlGeneralization` 定义的继承关系，而不考虑所有类都默认继承自 `Object` 这个情况。

定义继承深度为某类到其顶级父类之间，经过的直接继承次数。例如：若只有两个类 A 与 B，且 A 直接继承 B 时，A 的继承深度为 $1$；若只有一个类 A ，则 A 的继承深度为 $0$。

#### 关键状态

- 删除某个状态之后无法从 Initial State 到达任意一个 Final State，且不与后两条规定相悖，则该状态是关键状态；
- 如果状态机模型本来就无法从 Initial State 到达任意一个 Final State（包括 Final State 不存在的情况），则该状态机中所有状态都不是关键状态；
- Initial State 与 Final State 不是关键状态。

#### 某字段为空

指该字段是空指针 `null`，或仅包含**空白字符**（空格和制表符 `\t`）。

---

### 第四部分：题目描述

#### 一、作业要求

本次作业的程序主干逻辑（包括解析 `.mdj` 格式的文件为关键数据）均已实现，只需要同学们完成剩下的部分，即：**通过实现官方提供的接口，来实现自己的 UML 分析器**。

官方的**接口定义源代码**都已在接口源代码文件中给出，各位同学需要实现相应的官方接口，并保证**代码实现功能正确**。

具体来说，各位同学需要新建一个类，并实现相应的接口方法。

当然，还需要同学们**在主类中调用官方包的 `AppRunner` 类**，并载入自己实现的 UML 解析器类，来使得程序完整可运行，具体形式参考本次作业官方包目录下的 `README.md`。

##### 代码结构说明

`UserApi` 的具体接口规格见官方包的 jar 文件，此处不加赘述。

除此之外，`UserApi` 类必须实现一个构造方法

```java
public class MyImplementation implements UserApi {
    public MyImplementation(UmlElement[] elements);
}
```

或者

```java
public class MyImplementation implements UserApi {
    public MyImplementation(UmlElement... elements);
}
```

构造函数的逻辑为将 `elements` 数组内的各个 UML 元素传入 `MyImplementation` 类，以备后续解析。

请确保构造函数正确实现，且类和构造函数均定义为 public。`AppRunner` 内将自动获取此构造函数进行 `UserApi` 实例的生成。

（注：这两个构造方法实际本质上等价，不过后者实际测试使用时的体验会更好，想要了解更多的话可以百度一下，关键词：`Java 变长参数`）

##### 交互模式

- 调用上述构造函数，生成一个实例，并将 UML 模型元素传入；
- 之后将调用此实例的各个接口方法，以实现基于之前传入的 UML 模型元素的各类查询操作；
- 官方接口通过调用方法的返回值，自动生成对应的输出文本。

#### 二、关于类图的查询指令

> 该部分内容与上次作业完全相同。

各个指令对应的方法名和参数的表示方法详见官方接口说明。

##### 指令 1：模型中一共有多少个类

输入指令格式：`CLASS_COUNT`

举例：`CLASS_COUNT`

输出：

- `Total class count is x.`
  - 其中 `x` 为模型中类的总数。

##### 指令 2：类的子类数量

输入指令格式：`CLASS_SUBCLASS_COUNT classname`

举例：`CLASS_SUBCLASS_COUNT Elevator`

输出：

- `Ok, subclass count of class "classname" is x.`
  - 其中 `x` 为直接继承类 `classname` 的子类数量；
- `Failed, class "classname" not found.`
  - 不存在名为 `classname` 的类时，输出上述内容；
- `Failed, duplicated class "classname".`
  - 存在多个名为 `classname` 的类时，输出上述内容。

##### 指令 3：类中的操作有多少个

输入指令格式：`CLASS_OPERATION_COUNT classname`

举例：`CLASS_OPERATION_COUNT Elevator`

输出：

- `Ok, operation count of class "classname" is x.`
  - 其中 `x` 为类 `classname` 中的操作个数；
- `Failed, class "classname" not found.`
  - 不存在名为 `classname` 的类时，输出上述内容；
- `Failed, duplicated class "classname".`
  - 存在多个名为 `classname` 的类时，输出上述内容。

说明：

- 本指令中统计的一律为此类自己定义的操作，不包含继承自其各级父类所定义的操作；
- 本指令中统计的无需考虑**_重复操作_**带来的影响。若有多个操作为**_重复操作_**，则这些操作都需要分别计入答案。

##### 指令 4：类的操作可见性

输入指令格式：`CLASS_OPERATION_VISIBILITY classname methodname`

举例：`CLASS_OPERATION_VISIBILITY Taxi setStatus`

输出：

- `Ok, operation visibility of method "methodname" in class "classname" is public: www, protected: xxx, private: yyy, package-private: zzz.`
  - 其中 `www`/`xxx`/`yyy`/`zzz` 分别表示类 `classname` 中，名为 `methodname` 且实际可见性分别为 `public`/`protected`/`private`/`package-private` 的操作个数；
  - 如果类中不存在名为 `methodname` 的操作，则 `www`/`xxx`/`yyy`/`zzz` 全部设置为 0；
- `Failed, class "classname" not found.`
  - 不存在名为 `classname` 的类时，输出上述内容；
- `Failed, duplicated class "classname".`
  - 存在多个名为 `classname` 的类时，输出上述内容。

说明：

- 本指令中统计的一律为此类自己定义的操作，不包含继承自其各级父类所定义的操作；
- 在上一条的前提下，需要统计出全部的名为 `methodname` 的操作的可见性信息。
- 本指令中统计的无需考虑**_重复操作_**带来的影响。若有多个操作为**_重复操作_**，则这些操作都需要分别计入答案。

##### 指令 5：类的操作的耦合度

输入指令格式：`CLASS_OPERATION_COUPLING_DEGREE classname methodname`

举例：`CLASS_OPERATION_COUPLING_DEGREE Taxi setStatus`

输出：

- `Ok, method "methodname" in class "classname" has coupling degree: coupling_degree_1, coupling_degree_2, coupling_degree_3.`
  - 此例中，类中名为 `methodname` 的操作共有 3 个，它们的**_操作的耦合度_**分别为 `coupling_degree_1`、`coupling_degree_2`、`coupling_degree_3`，且这些操作中不存在**_重复操作_**；
  - 传出列表时可以乱序，官方接口会自动进行排序（但是需要编写者自行保证不重不漏）；
  - 如果类中不存在名为 `methodname` 的操作，则传出一个空列表；
- `Failed, class "classname" not found.`
  - 不存在名为 `classname` 的类时，输出上述内容；
- `Failed, duplicated class "classname".`
  - 存在多个名为 `classname` 的类时，输出上述内容；
- `Failed, wrong type of parameters or return value in method "methodname" of class "classname".`
  - 类 `classname` 中所有名为 `methodname` 的操作中，存在某个操作具有**_错误类型_**时，输出上述内容；
- `Failed, duplicated method "methodname" in class "classname".`
  - 类 `classname` 中所有名为 `methodname` 的操作存在**_重复操作_**时，输出上述内容。

说明：

- 本指令中统计的一律为此类自己定义的操作，不包含继承自其各级父类所定义的操作；
- 如果同时存在**_错误类型_**和**_重复操作_**两种异常，按**_错误类型_**异常处理。

##### 指令 6：类的属性的耦合度

输入指令格式：`CLASS_ATTR_COUPLING_DEGREE classname`

举例：`CLASS_ATTR_COUPLING_DEGREE Taxi`

输出：

- `Ok, attributes in class "classname" has coupling degree x.`
  - 其中 `x` 为类 `classname` 的**_属性的耦合度_**
- `Failed, class "classname" not found.`
  - 不存在名为 `classname` 的类时，输出上述内容；
- `Failed, duplicated class "classname".`
  - 存在多个名为 `classname` 的类时，输出上述内容。

说明：

- 本指令的查询需要考虑继承自其各级父类所定义的属性，但**不需要**考虑实现的接口所定义的属性（无论是直接实现还是通过父类或者接口继承等方式间接实现，都算做实现了接口）；
- 本查询中忽略属性名称相同的错误。

##### 指令 7：类实现的全部接口

输入指令格式：`CLASS_IMPLEMENT_INTERFACE_LIST classname`

举例：`CLASS_IMPLEMENT_INTERFACE_LIST Taxi`

输出：

- `Ok, implement interfaces of class "classname" are (A, B, C).`
  - 此例中，类 `classname` 实现了 `A`、`B`、`C` 这 3 个接口；
  - 无论是直接实现还是通过父类或者接口继承等方式间接实现，都算做实现了接口；
  - 传出列表时可以乱序，官方接口会自动进行排序（但是需要编写者自行保证不重不漏）；
  - 如果类 `classname` 没有实现任何接口，则传出一个空列表；
- `Failed, class "classname" not found.`
  - 不存在名为 `classname` 的类时，输出上述内容；
- `Failed, duplicated class "classname".`
  - 存在多个名为 `classname` 的类时，输出上述内容。

##### 指令 8：类的继承深度

输入指令格式：`CLASS_DEPTH_OF_INHERITANCE classname`

举例：`CLASS_DEPTH_OF_INHERITANCE AdvancedTaxi`

输出：

- `Ok, depth of inheritance of class "classname" is x.`
  - 其中 `x` 为类 `classname` 的继承深度；
- `Failed, class "classname" not found.`
  - 不存在名为 `classname` 的类时，输出上述内容；
- `Failed, duplicated class "classname".`
  - 存在多个名为 `classname` 的类时，输出上述内容。

#### 三、关于 UML 状态图的查询指令

> 除了如下改动：
>
> - 用**_某字段为空_**的定义等价替换了原有的定义（含义未改变，仅为了统一说明）
>
> 其余部分内容与上次作业完全相同。

##### 指令 1：给定状态机模型中一共有多少个状态

输入指令格式：`STATE_COUNT statemachine_name`

举例：`STATE_COUNT complex_sm`

输出：

- `Ok，state count of statemachine "statemachine_name" is x.`
  - 其中 `x` 为状态机模型 `statemachine_name`（UMLStateMachine）中的状态个数；
- `Failed, statemachine "statemachine_name" not found.`
  - 不存在名为 `statemachine_name` 的状态机模型时，输出上述内容；
- `Failed, duplicated statemachine "statemachine_name".`
  - 存在多个名为 `statemachine_name` 的状态机模型时，输出上述内容。

说明：

- Initial State 和 Final State 均算作状态。

##### 指令 2：给定状态机模型和其中的一个状态，判断其是否是关键状态

输入指令格式：`STATE_IS_CRITICAL_POINT statemachine_name statename`

举例：`STATE_IS_CRITICAL_POINT complex_sm open`

输出：

- `Ok, state "statename" in statemachine "statemachine_name" is a critical point.`
  - 状态机模型 `statemachine_name` 中的 `statename` 状态是**_关键状态_**时，输出上述内容；
- `Ok, state "statename" in statemachine "statemachine_name" is not a critical point.`
  - 状态机模型 `statemachine_name` 中的 `statename` 状态不是**_关键状态_**时，输出上述内容；
- `Failed, statemachine "statemachine_name" not found.`
  - 不存在名为 `statemachine_name` 的状态机模型时，输出上述内容；
- `Failed, duplicated statemachine "statemachine_name".`
  - 存在多个名为 `statemachine_name` 的状态机模型时，输出上述内容；
- `Failed, state "statename" in statemachine "statemachine_name" not found.`
  - 状态机模型 `statemachine_name` 中不存在名为 `statename` 的状态时，输出上述内容；
- `Failed, duplicated state "statename" in statemachine "statemachine_name".`
  - 状态机模型 `statemachine_name` 中存在多个名为 `statename` 的状态时，输出上述内容。

##### 指令 3：给定状态机模型和其中两个状态，引起状态迁移的所有触发事件

输入指令格式：`TRANSITION_TRIGGER statemachine_name statename1 statename2`

举例：`TRANSITION_TRIGGER door_sm open close`

输出：

- `Ok，triggers of transition from state "statename1" to state "statename2" in statemachine "statemachine_name" are (A, B, C).`
  - 此例中，引起状态机模型 `statemachine_name` 从 `statename1` 迁移到 `statename2` 的事件共有 3 个，分别为 `A`、`B`、`C`；
  - 传出列表时可以乱序，官方接口会自动进行排序（但是需要编写者自行保证不重不漏）；
- `Failed, statemachine "statemachine_name" not found.`
  - 不存在名为 `statemachine_name` 的状态机模型时，输出上述内容；
- `Failed, duplicated statemachine "statemachine_name".`
  - 存在多个名为 `statemachine_name` 的状态机模型时，输出上述内容；
- `Failed, state "statename1" in statemachine "statemachine_name" not found.`
  - 状态机模型 `statemachine_name` 中不存在名为 `statename1` 的状态时，输出上述内容；
- `Failed, duplicated state "statename1" in statemachine "statemachine_name".`
  - 状态机模型 `statemachine_name` 中存在多个名为 `statename1` 的状态时，输出上述内容；
- `Failed, transition from state "statename1" to state "statename2" in statemachine "statemachine_name" not found.`
  - 状态机模型 `statemachine_name` 中未找到任何从状态 `statename1` 到状态 `statename2` 的迁移时，输出上述内容。

说明：

- 该询问考虑的迁移为状态间的**直接迁移**；
- 检测状态与迁移异常时，先检测起点状态是否存在异常，再检测终点状态是否存在异常，最后检查是否存在相应的迁移；
- 任意两个状态间有零个或多个迁移；
- 我们保证对于每个非 Initial State 到非 Initial State 的迁移，都至少有一个触发事件；
- 一个迁移上的所有触发事件名称两两不同，且不**_为空_**。

#### 四、关于 UML 顺序图的查询指令

> 该部分内容与上次作业完全相同。

##### 指令 1：给定 UML 顺序图，一共有多少个参与对象

输入指令格式：`PTCP_OBJ_COUNT umlinteraction_name`

举例：`PTCP_OBJ_COUNT normal`

输出：

- ` Ok, participant count of umlinteraction "umlinteraction_name" is x.`
  - 其中 `x` 为顺序图模型 `umlinteraction_name`（UMLInteraction）中的参与对象（UMLLifeline）个数；
- `Failed, umlinteraction "umlinteraction_name" not found.`
  - 不存在名为 `umlinteraction_name` 的顺序图模型时，输出上述内容；
- `Failed, duplicated umlinteraction "umlinteraction_name".`
  - 存在多个名为 `umlinteraction_name` 的顺序图模型时，输出上述内容。

##### 指令 2：给定 UML 顺序图和参与对象，找出能创建该参与对象的另一个参与对象

输入指令格式：`PTCP_CREATOR umlinteraction_name lifeline_name`

举例：`PTCP_CREATOR normal door`

输出：

- `Ok, lifeline "lifeline_name" in umlinteraction "umlinteraction_name" can be created by "creator_name".`
  - 其中 `creator_name` 为顺序图模型 `umlinteraction_name` 中能创建 `lifeline_name` 的参与对象；
- `Failed, umlinteraction "umlinteraction_name" not found.`
  - 不存在名为 `umlinteraction_name` 的顺序图模型时，输出上述内容；
- `Failed, duplicated umlinteraction "umlinteraction_name".`
  - 存在多个名为 `umlinteraction_name` 的顺序图模型时，输出上述内容。
- `Failed, lifeline "lifeline_name" in umlinteraction "umlinteraction_name" not found.`
  - 顺序图模型 `umlinteraction_name` 中不存在名为 `lifeline_name` 的参与对象时，输出上述内容；
- `Failed, duplicated lifeline "lifeline_name" in umlinteraction "umlinteraction_name".`
  - 顺序图模型 `umlinteraction_name` 中存在多个名为 `lifeline_name` 的参与对象时，输出上述内容；
- `Failed, lifeline "lifeline_name" in umlinteraction "umlinteraction_name" is never created.`
  - 顺序图模型 `umlinteraction_name` 中的参与对象 `lifeline_name` 没有收到创建消息时，输出上述内容；
- `Failed, lifeline "lifeline_name" in umlinteraction "umlinteraction_name" is created repeatedly.`
  - 顺序图模型 `umlinteraction_name` 中的参与对象 `lifeline_name` 收到多条创建消息时，输出上述内容。

说明：

- 测试数据中不会出现 Endpoint 向 Lifeline 发送 Create Message 的情况。

##### 指令 3：给定 UML 顺序图和参与对象，收到了多少个 Found 消息，发出了多少个 Lost 消息。

输入指令格式：`PTCP_LOST_AND_FOUND umlinteraction_name lifeline_name`

举例：`PTCP_LOST_AND_FOUND normal door`

输出：

- `Ok, incoming found message and outgoing lost message count of lifeline "lifeline_name" of umlinteraction "umlinteraction_name" is x and y.`
  - 其中 `x` 为顺序图模型 `umlinteraction_name`（UMLInteraction）中 `lifeline_name` 收到的 Found 的消息个数，`y` 为发送的 Lost 消息个数；
- `Failed, umlinteraction "umlinteraction_name" not found.`
  - 不存在名为 `umlinteraction_name` 的顺序图模型时，输出上述内容；
- `Failed, duplicated umlinteraction "umlinteraction_name".`
  - 存在多个名为 `umlinteraction_name` 的顺序图模型时，输出上述内容。
- `Failed, lifeline "lifeline_name" in umlinteraction "umlinteraction_name" not found.`
  - 顺序图模型 `umlinteraction_name` 中不存在名为 `lifeline_name` 的参与对象时，输出上述内容；
- `Failed, duplicated lifeline "lifeline_name" in umlinteraction "umlinteraction_name".`
  - 顺序图模型 `umlinteraction_name` 中存在多个名为 `lifeline_name` 的参与对象时，输出上述内容；

说明：

- Found 消息为来自 Endpoint 的消息，Lost 消息为发送至 Endpoint 的消息。

#### 五、模型有效性检查

> 该部分为新增指令。

模型有效性检查部分，将在**实例化完毕后自动按序触发执行**，而不需要通过指令的形式执行。执行中一旦**发现不符合规则的情况，将直接退出，不进行后续有效性检查和指令查询**。

##### R001: 类图元素名字不能为空（UML 001）

规则解释：

- 目前所有**类图**的元素中，除了以下元素之外，其余元素的 `name` 字段均不能**_为空_**：

  - `direction` 为 `return` 的 UMLParameter
  - UMLAssociation
  - UMLAssociationEnd
  - UMLGeneralization
  - UMLInterfaceRealization

输出：

- `Failed when check R001, a certain element doesn't have name.`
  - 如未发现此问题，则不需要任何输出，否则输出上述内容。

##### R002：针对下面给定的模型元素容器，不能含有重名的成员（UML 002）

规则解释：

- 针对类图中的类（UMLClass），其成员属性（UMLAttribute）和关联的另一端所连接的 UMLAssociationEnd 这两者构成的整体中，不能有重名的成员。

输出：

- `Failed when check R002, "member" in "Container", "member2" in "AnotherContainer" has duplicated name.`
  - 如未发现此问题，则不需要任何输出，否则输出上述内容；
  - 需要输出所有重名的成员名，以及它们所在的类。此例中，一共有两个存在重名的成员，分别是 `Container` 类中的 `member`，与 `AnotherContainer` 类中的 `member2`。

说明：

- 如果一个类中有多个同名的成员，则这些成员名只需要输出一次；
- 如果模型中有多个模型元素违背 R002，则依次输出，次序不敏感，接口会在输出前进行排序；
- 此规则无需考虑继承关系，也不需要考虑接口实现关系；
- 一个类下的属性和关联的另一端所连接的 UMLAssociationEnd 也不可出现重名。注意理解**关联的另一端**的意思；
- 特殊规定：若有两个 UMLAssociationEnd 的 `name` 字段都**_为空_**，则规定这两个成员不是重名。

##### R003：不能有循环继承（UML008）

规则解释：

- 该规则只考虑类的继承关系以及接口之间的继承关系。所谓循环继承，就是按照继承关系形成了环。
- 例如下面的场景：

  ```java
  interface A extends B {
      // something here
  }

  interface B extends A {
      // something here
  }
  ```

  这里就构成了一组最简单的循环继承。

输出：

- `Failed when check R003, class/interface (A, B, C, D) have circular inheritance.`

  - 如未发现此问题，则不需要任何输出，否则输出上述内容；
  - 需要列出所有在循环继承链中的类或接口名。此例中，一共有 4 个存在循环继承的类或接口，分别是 A、B、C、D。

说明：

- 对于同一个类和接口，只需要输出一次即可；
- 如果模型中有多个模型元素违背 R003，则依次输出，次序不敏感，接口会在输出前进行排序；
- 输出的集合中需要包含全部继承环上的类和接口。

##### R004：任何一个类或接口不能重复继承另外一个类或接口（UML007）

规则解释：

- 该规则考虑类之间的继承关系、接口之间的继承关系，包括直接继承或间接继承。
- 例如下面的场景

  ```java
  interface A {
      // something here
  }

  interface B extends A {
      // something here
  }

  interface C extends A, B {
      // something here
  }
  ```

  接口 C 就重复继承了接口 A（一次直接继承，一次通过接口 B 间接继承）。

输出：

- `Failed when check R004, class/interface (A, B, C, D) have duplicated generalizations.`

  - 如未发现此问题，则不需要任何输出，否则输出上述内容；
  - 需要列出所有带有重复继承的类或者接口名。此例中，一共有 4 个存在重复继承的类或接口，分别是 A、B、C、D。

说明：

- 如果存在多个直接或间接重复继承了其他的类或接口的类或接口，则按照任意顺序传出即可，次序不敏感，接口会在输出前进行排序。
- 值得注意的是，**本次作业的本条限制，同样也禁止了接口的重复继承**。然而接口重复继承在 Java 8 中实际上是允许的，也就是说，这是 UML 本身的一条合法性规则，无关语言。请各位判断的时候务必注意这件事。

##### R005: 接口的所有属性均需要为 public（UML 011）

规则解释：

- 接口属性的可见性需要为`public`。

输出：

- `Failed when check R005, all attributes and operations of interface must be public.`
  - 如未发现此问题，则不需要任何输出，否则输出上述内容。

说明：

- 在我们的模型中，接口不会有方法，因此只需要检测属性。

##### R006：Lifeline 必须表示在同一 Sequence Diagram 中定义的 Attribute

规则解释：

- Lifeline 的 `represent` 属性必须指向在同一 Sequence Diagram 下定义的 `Attribute`。

输出：

- `Failed when check R006, each lifeline must represent an attribute.`
  - 如未发现此问题，则不需要任何输出，否则输出上述内容。

##### R007：一个 Lifeline 在被销毁后不能再收到任何消息

规则解释：

- 一个 `Lifeline` 是一个实例对象，在被销毁（即收到 Delete 消息）后再收到任何消息都是不合理的。

输出：

- `Failed when check R007, a lifeline receives messages after receiving a delete message.`
  - 如未发现此问题，则不需要任何输出，否则输出上述内容。

说明：

- 在官方包导出的模型中，消息的顺序与输入的顺序相同。越早输入的 UMLMessage 元素，代表了越早的消息。

##### R008：所有 Final state 状态不能有任何迁出（UML 033）

规则解释：

- 所有 Final state 不能有任何迁出。

输出：

- `Failed when check R008, a final vertices has at least one outgoing transition.`
  - 如未发现此问题，则不需要任何输出，否则输出上述内容。

##### R009：一个状态不能有两个条件相同的迁出

规则解释：

- 如果存在一个状态的所有的迁出 Transition 的所有触发事件（Trigger）中有两个相同的 Trigger，那么这两个 Trigger 所在的 Transition 必须拥有不**_为空_**且逻辑上不能同时成立的守护条件（Guard）；
- 如果不满足这条规则，就会存在某种可能性，使得从这个状态开始不知道走哪一个转移。

输出：

- `Failed when check R009, a state has ambiguous outgoing transition.`
  - 如未发现此问题，则不需要任何输出，否则输出上述内容。

说明：

- 为了简化问题，将“逻辑上不能同时成立的 Guard”解释为“字符串比较不相同”；
- 为了简化问题，将“两个 Trigger 相同”解释为“它们的 `name` 字段字符串相同”。

---

### 第五部分：设计建议

- 推荐各位同学在课下测试时使用 Junit 单元测试来对自己的程序进行测试
  - Junit 是一个单元测试包，**可以通过编写单元测试类和方法，来实现对类和方法实现正确性的快速检查和测试**。还可以查看测试覆盖率以及具体覆盖范围（精确到语句级别），以帮助编程者全面无死角的进行程序功能测试。
  - Junit 已在评测机中部署（版本为 Junit4.12，一般情况下确保为 Junit4 即可），所以项目中可以直接包含单元测试类，在评测机上不会有编译问题。
  - 此外，Junit 对主流 Java IDE（Idea、eclipse 等）均有较为完善的支持，可以自行安装相关插件。推荐两篇博客：
    - [Idea 下配置 Junit](https://www.cnblogs.com/wangmingshun/p/6411885.html)
    - [Idea 下 Junit 的简单使用](https://blog.csdn.net/yitengtongweishi/article/details/80715569)
  - 感兴趣的同学可以自行进行更深入的探索，百度关键字：`Java Junit`。
- 强烈推荐同学们
  - 去阅读本次的源代码
  - **好好复习下上次和本次的 ppt，并理清楚各个 `UmlElement` 数据模型的结构与关系**。

---

### 第六部分：输入/输出说明

本次作业将会下发 mdj 文件解析工具、`UserApi` 类、输入输出接口（实际上为二合一的工具，接口文档会详细说明）和全局测试调用程序，其中输入输出接口、全局测试程序均在官方接口中。

- 解析工具用于将 mdj 格式文件解析为输入输出接口可以识别的格式，该格式包含了文件内模型中所有关键信息的元素字典表；
- 输入输出接口用于对元素字典表的解析和处理、对查询指令的解析和处理以及对输出信息的处理；
- 全局测试调用程序会实例化同学们实现的类，并根据输入接口解析内容调用对应方法，并把返回结果通过输出接口进行输出。

输入输出接口的具体字符格式已在接口内部定义好，各位同学可以阅读相关代码，这里只给出程序黑箱的字符串输入输出。

#### 输入输出规则

- 输入一律在标准输入中进行，输出一律向标准输出中输出；
- 输入内容以指令的形式输入，一条指令占一行，输出以提示语句的形式输出，一句输出占一行；
- 输入使用官方提供的输入接口，输出使用官方提供的输出接口；
- 输入的整体格式如下：
  - 由 `.mdj` 文件解析而来的关键元素表；
  - `END_OF_MODEL` 分隔开行；
  - 指令序列，每条指令一行。

#### 输入样例 & 输出样例

由于样例较多，详细样例请参考本次作业的开源库，分别对应违反 R001 ~ R009 的情况。

#### 一、公测说明

`.mdj` 文件内容限制：

- 可能包含的种类：
  - 包含类图，并在 UMLModel 内进行建模，且每个 UMLModel 内的元素不会引用当前 UMLModel 以外的元素（即关系是一个闭包）；
  - 包含顺序图，与 UMLModel 平级，可能会引用到 UMLModel 中的模型元素；
  - 包含状态图，与 UMLModel 平级，不会引用 UMLModel 中的其他模型元素；
  - 一个 `.mdj` 文件中，除了类图至多有一个外，其余类型的图的数量没有限制。
- 原始 `.mdj` 文件仅通过 StarUML 工具建模生成（不存在手改 `json`等行为），符合 StarUML 规范，可在 StarUML 中正常打开和显示；
- `.mdj` 文件中最多只包含 300 个元素；
- `.mdj` 各元素字段值限制见**第八部分：附录**；
- 此外为了方便本次的情况处理，保证所建模的类图模型，在通过检查的情况下，均可以在 Oracle Java 8 中正常实现出来；如果没有通过检查，除了需要检查的错误外，其余均符合 Oracle Java 8 标准；
- 每个数据均可按照前述条件找到唯一一个错误。

输入指令限制：

- 最多不超过 200 条指令；
- 输入指令满足标准格式。

测试数据限制：

- 全局限制
  - 所有公测数据不会对接口中定义的方法、类属性（static attribute）、类方法（static method）做任何测试要求。
- 类图相关
  - 对于多继承问题，我们保证在类图数据中，类一定没有多继承，但是接口可能有多继承（即与 Java 8 规范相同）。
- 顺序图相关
  - 无相关保证。
- 状态图相关
  - 保证每个 State Machine 中有且仅有一个 Region；
  - 保证每个 State Machine 中，有且仅有一个 Initial State，有零个或多个 Final State；
  - 保证每个 State Machine 中 Initial State 和 Final State 的 name 均为 null，查询指令中给出的状态也不会为 Initial State 或 Final State；
  - 保证每个 State Machine 中，Initial State 没有状态迁入；
  - 保证每个 State Machine 中不包含复合状态。

测试模式：

- 公测均通过标准输入输出进行；
- 指令将会通过查询 UML 类图、状态图、顺序图各种信息的正确性，从而测试 UML 解析器各个接口的实现正确性；
- 对于任何满足基本数据限制的输入，程序都应该保证不会异常退出，如果出现问题则视为未通过该测试点；
- 程序的最大运行 CPU 时间为 10s，保证强测数据有一定梯度。

#### 二、互测说明

本次作业**不设置互测环节**。针对本次作业提交的代码实现，课程将使用公测 + bug 修复的黑箱测试模式。

---

### 第七部分：提示与警示

#### 一、提示

- 本次作业中可以自行组织工程结构。任意新增 `java` 代码文件。只需要保证 `UserApi` 类的继承与实现即可。
- **关于本次作业解析器类的设计具体细节，本指导书中均不会进行过多描述，请自行去官方包开源仓库中查看接口的规格，并依据规格进行功能的具体实现**，必要时也可以查看 AppRunner 的代码实现。关于官方包的使用方法，可以去查看开源库的`README.md`。
- **如果同时满足多个异常，在查询上层模型发生“异常”后，我们自然不该再去查询这个“异常层次”的下层次模型。**
- [开源库地址](http://gitlab.oo.buaa.edu.cn/2022_public/guidebook/homework_15)

关于本次作业新增指令：

- 本次作业的有效性检测基于 StarUML 的有效性检测，但出于易实现性和作业难度的考虑，对原规则进行了一定的修改。因此，在 StarUML 中检测出的 Validation Results 仅为参考。
- StarUML 官方文档中关于有效性检查的部分：[传送门](https://staruml.readthedocs.io/en/latest/reference/uml-validation-rules.html)

#### 二、警示

- **不要试图通过反射机制来对官方接口进行操作**，我们有办法进行筛查。此外，如果发现有人试图通过反射等手段 hack 输出接口的话，请邮件 `18374457@buaa.edu.cn` 或使用微信向助教进行举报，**经核实后，将直接作为无效作业处理**。

---

### 第八部分：附录

> 该部分内容与上次作业完全相同。

#### 标准输入限制说明

下面给出了标准输入在经过官方接口转换后生成的各种对象中各种字段的格式限制。

首先，对所有 **`UmlElement`** 子类以及所有实现 **`NameableType`** 接口的类的以下字段有通用规定，不再在后面赘述：

- 所有的 `id` 字段都是不为 `null` 的字符串，且在主函数中传入的 `UmlElement` 列表中唯一。
- 除额外说明，所有的 `name` 字段**都不作任何保证**，即均可能为 `null`，或空字符串 `""`，或有其他内容的字符串。
- 规定~~类、操作、属性、非返回值的参数、接口、~~生命线、消息、状态（不包含起止状态）、顺序图模型、状态机模型等对象的名称不能为 `null`。
- 所有的 `visibility` 字段都是不为 `null` 的枚举对象。
- 若字段 X 的格式说明是 "**_None_**"：**对该字段不作任何保证**，可能为 `null` 或者该类型的对象。
- 若字段 X 的格式说明是 "**_NotNull_**"： 保证该字段不可能为 `null`， 仅可能是类型的对象。

有某些字段是代表指向其他 `UmlElement` 的字符串格式的 ID，如 `parentId`、`end1`、`source` 等等，为了简洁地说明特做出以下规定：

- 若某 `String` 类型字段 S 的格式说明形如 "**_UmlOperation_**" : 则 S 不为 `null`，且在传入的 `UmlElement` 列表中存在唯一一个 `id` 等于 S 的对象，且该对象的类型是 `UmlOperation`。
- 若某 `String` 类型字段 S 的格式说明形如 "**_UmlClass | UmlInterface_**"：则 S 不为 `null`，且在传入的 `UmlElement` 列表中存在唯一一个 `id` 等于 S 的值的对象，且该对象的类型是 `UmlClass` **或者** `UmlInterface`。

#### UML 类图相关元素格式限制

##### UmlClass

- parentId：**_None_**

##### UmlOperation

- parentId：**_UmlClass_**

##### UmlAttribute

- parentId：**_UmlClass | UmlInterface | UmlCollaboration_**
- type：**_NotNull_**

##### UmlParameter

- parentId：**_UmlOperation_**
- type：**_NotNull_**
- direction： IN | RETURN

##### ReferenceType

- referenceId：**_UmlClass | UmlInterface_**

##### UmlAssociation

- parentId：**_None_**
- end2：**_UmlAssociationEnd_**
- end1：**_UmlAssociationEnd_**

##### UmlAssociationEnd

- parentId：**_UmlAssociation_**
- reference：**_UmlClass | UmlInterface_**
- multiplicity：**_NotNull_**
- aggregation：**_NotNull_**

##### UmlInterface

- parentId：**_None_**

##### UmlInterfaceRealization

- parentId：**_None_**
- source：**_UmlClass_**
- target：**_UmlInterface_**

##### UmlGeneralization

- parentId：**_None_**
- source：**_UmlClass | UmlInterface_**
- target：**_UmlClass | UmlInterface_**
- 注：source 和 target 指向的元素类型一定相同。

#### UML 顺序图相关元素格式限制

##### UmlCollaboration

- parentId：**_None_**

##### UmlInteraction

- parentId：**_UmlCollaboration_**

##### UmlLifeline

- parentId：**_UmlInteraction_**
- represent：**_UmlAttribute_**

##### UmlMessage

- parentId：**_UmlInteraction_**
- source：**_UmlLifeline | UmlEndPoint_**
- target：**_UmlLifeline | UmlEndPoint_**
- messageSort：**_NotNull_**

##### UmlEndPoint

- parentId：**_UmlInteraction_**

#### UML 状态图相关元素格式限制

##### UmlStateMachine

- parentId：**_None_**

##### UmlRegion

- parentId：**_UmlStateMachine_**

##### UmlPseudostate

- parentId：**_UmlRegion_**

##### UmlState

- parentId：**_UmlRegion_**

##### UmlFinalState

- parentId：**_UmlRegion_**

##### UmlTransition

- parentId：**_UmlRegion_**
- source：**_UmlPseudostate | UmlState | UmlFinalState_**
- target：**_UmlPseudostate | UmlState | UmlFinalState_**
- guard：**_None_**

##### UmlEvent

- parentId：**_UmlTransition_**
- value：**_None_**
- expression：**_None_**

##### UmlOpaqueBehavior

- parentId：**_UmlTransition_**
