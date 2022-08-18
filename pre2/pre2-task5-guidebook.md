## 面向对象设计与构造预习作业2-5

### 第一部分：训练目标

学习接口相关知识，并实践如何使用接口来建立行为层次结构。

----

### 第二部分：预备知识

#### 一、接口

前面我们提到了子类可以重写父类的方法，这使得子类的方法可以在父类的方法的基础上增加功能，或者实现一套和父类不同的新的功能。

倘若父类的**抽象程度**很高，以至于在父类中没有办法去编写一个实现具体功能的方法，我们可能会想是不是可以不写方法的具体实现语句，只定义方法签名呢？

比方说，正方形和圆形的面积计算很具体，假设为正方形和圆形建立了一个共同的抽象父类二维图形，此时如何去实现一个二维图形的面积呢？

比如下面的例子：

```java
class Square {
    private double length;
    public double getArea() { //你可以为一个正方形编写求面积方法
        return length * length;
    }
}

class Circle {
    private double radius;
    public double getArea() { //你可以为一个圆形编写求面积方法
        return radius * radius * Math.PI;
    }
}
```

很显然，我们无法为抽象的二维图形Shape类实现面积求解方法。此时，我们可以使用接口(Interface)来表示这个抽象的类，然后声明上述两个具体的类实现(implements)了这个接口：

```java
interface Shape {
    public double getArea(); // 你不能为抽象的`形状`概念定义求面积方法
}

class Square implements Shape {
    private double length;
    public Square(double length) {
        this.length = length;
    }
    @Override
    public double getArea() { //你可以为一个正方形编写求面积方法
        return length * length;
    }
}

class Circle implements Shape {
    private double radius;
    public Circle(double radius) {
        this.radius = radius;
    }
    @Override
    public double getArea() { //你可以为一个圆形编写求面积方法
        return radius * radius * Math.PI;
    }
}

```

之后，你可以用接口类型来引用实现了该接口的任意类型的实例化对象，并调用接口所声明的方法。需要注意的是，你不能用接口类型来**实例化**一个对象：

```java
class Main {
    public static void main(String[] args) {
        Shape myShape; // 声明一个Shape的变量， 这是还没有任何实例产生
        myShape = new Square(888); // 创建一个Square的实例，用myShape变量引用它。
        System.out.println(myShape.getArea());
        myShape = new Circle(888); // 创建一个Circle的实例，用myShape变量引用它。
        System.out.println(myShape.getArea());
        myShape = new Shape(); // Shape的概念过于抽象以至于实例化没有意义，这一行编译报错。

    }
}

```

需要注意的是，接口提供了行为的抽象机制。在上面的例子中，Square和Circle的共性在于其行为操作，因而使用接口是合适的。对于其他一些情况，多个类之间可能即有共性的行为，也有共性的数据属性，此时使用类建立抽象层次更加合适。

在编程时，尽量使用高层次的引用（比如抽象类的引用和接口的引用），避免使用实际子类型的引用的方式，叫做面向抽象编程。下面我们会通过本 Task 让大家体会这一点。

----

### 第三部分：基本要求

在本任务中，我们允许**冒险者雇佣并使用另一个冒险者**，且**赋予冒险者价值的概念**，把装备和冒险者都看作是**价值体**。

----

### 第四部分：题目描述

- 在 Task4 的基础上，我们定义冒险者的价值 `price` 为**其拥有的所有价值体的价值之和**，即冒险者的价值是其**装备**的价值及其**雇佣的冒险者**的价值的和。
- 在 Task4 的基础上，增加冒险者之间的**雇佣关系**：冒险者 A 雇佣冒险者 B，可以认为是把冒险者 B 看成一种**价值体**。此时冒险者 A 拥有价值体冒险者 B，之后冒险者 A 便可以像使用其他装备一样**使用**冒险者 B。
- 在Task4的基础上，定义**冒险者 A 使用冒险者 B**，其效果为冒险者 A **按照价值从大到小、价值相同则按价值体 `id` 从大到小的顺序（同 Task4）** 依次使用**冒险者 B 的价值体**，价值体的价值指的是所有价值体在**本次使用前**的价值。我们规定：如果当前使用到了冒险者 B 雇佣的冒险者 C，则冒险者 C 要按照如上顺序使用其拥有的价值体，这些价值体将作用于最开始使用的冒险者，在此处即为冒险者 A。

----


### 第五部分：输入/输出格式

第一行一个整数 $m$，表示操作的个数。

接下来的 $m$ 行，每行一个形如 `{type} {attribute}` 的操作，操作输入形式及其含义如下：

- 对 Task4 中的一些指令进行**少量修改**，**重点地方已经加粗**，并新增一条指令 10：

| type | attribute                                                    | 指令含义                                                     | 输出                                                         |
| ---- | ------------------------------------------------------------ | ------------------------------------------------------------ | ------------------------------------------------------------ |
| 1    | `{adv_id} {name}`                                            | 加入一个 ID 为 `{adv_id}`、名字为 `{name}` 的冒险者，且未持有任何装备 | 无                                                           |
| 2    | `{adv_id} {equipment_type} {vars}（equipment_type和vars的含义见下表）` | 给予某个人某件装备，装备类型由 `{equipment_type}` 定义，属性由 `{vars}` 定义，所有的瓶子初始默认装满 | 无                                                           |
| 3    | `{adv_id} {id}`                                              | 删除 ID 为 `{adv_id}` 的冒险者的 ID 为 `{id}` 的**价值体**<br/>如果被删除的价值体是冒险者，则解除雇佣关系，后续无法使用该被被解除了雇佣关系的冒险者<br/>如果删除的价值体是装备，则丢弃该装备，后续该冒险者无法使用该装备 | 无              |
| 4    | `{adv_id}`                                                   | 查询 ID 为 `{adv_id}` 的冒险者所持有**价值体**的价格之和<br/>如果价值体是装备，则价值就是 `price` <br/>如果价值体是冒险者，则其价值计算按照本 Task 最开始定义的规则 | 一个整数，表示某人所有**价值体**的价值总和                   |
| 5    | `{adv_id}`                                                   | 查询 ID 为 `{adv_id}` 的冒险者所持有**价值体**价格的最大值<br>如果价值体是装备，则价值就是 `price` <br>如果价值体是冒险者，则其价值计算按照本 Task 最开始定义的规则 | 一个整数，表示该冒险者所有**价值体**价格的最大值             |
| 6    | `{adv_id}`                                                   | 查询 ID 为 `{adv_id}` 的冒险者所持有的价值体总数<br>如果价值体是装备，则对总数的贡献是 1<br>如果价值体是冒险者，则**只要考虑被雇佣冒险者本身这一个价值体**即可，不需要考虑被雇佣冒险者所拥有的其他价值体，即对总数的贡献也是 1。 | 一个整数，表示某人所有**价值体**的数量之和                   |
| 7    | `{adv_id} {commodity_id}`                                    | 打印 ID 为 `{commodity_id}` 的**价值体**的全部属性           | 该**价值体**的全部属性，格式见下文“属性打印方式”             |
| 8    | `{adv_id}`                                                   | ID 为 `adv_id` 的冒险者按照价值**由大到小**的顺序使用其全部**价值体**，若价值相同则按照价值体的 `id` **由大到小**的顺序使用。（ 价值体价值为所有价值体**本次使用前的价值**）<br>如果当前使用的是冒险者价值体，则按照上述顺序使用该冒险者价值体拥有的价值体 | 每个**价值体**在使用时就会产生输出，除此之外无额外输出       |
| 9    | `{adv_id}`                                                   | 打印 ID 为 `{adv_id}` 的冒险者的当前状态。                   | 一个字符串表示冒险者的状态：<br />The adventurer's id is {adv_id}, name is {name}, health is {health}, exp is {exp}, money is {money}. |
| 10   | `{adv_id1} {adv_id2}`                                        | ID 为`adv_id1`的冒险者雇佣 ID 为`adv_id2`的冒险者            | 无                                                           |

`vars` 和 `equipment_type` 如下：

| 装备类型      | equipment_type | vars                                  |
| ------------- | -------------- | ------------------------------------- |
| Bottle        | 1              | id name price capacity                |
| HealingPotion | 2              | id name price capacity efficiency     |
| ExpBottle     | 3              | id name price capacity expRatio       |
| Sword         | 4              | id name price sharpness               |
| RareSword     | 5              | id name price sharpness extraExpBonus |
| EpicSword     | 6              | id name price sharpness evolveRatio   |

属性打印方式表格：

| 价值体类型             | 属性打印方式                                                 |
| ---------------------- | ------------------------------------------------------------ |
| Bottle                 | The bottle's id is {id}, name is {name}, capacity is {capacity}, filled is {filled}. |
| HealingPotion          | The healingPotion's id is {id}, name is {name}, capacity is {capacity}, filled is {filled}, efficiency is {efficiency}. |
| ExpBottle              | The expBottle's id is {id}, name is {name}, capacity is {capacity}, filled is {filled}, expRatio is {expRatio}. |
| Sword                  | The sword's id is {id}, name is {name}, sharpness is {sharpness}. |
| RareSword              | The rareSword's id is {id}, name is {name}, sharpness is {sharpness}, extraExpBonus is {extraExpBonus}. |
| EpicSword              | The epicSword's id is {id}, name is {name}, sharpness is {sharpness}, evolveRatio is {evolveRatio}. |
| **Adventurer**（新增） | The adventurer's id is {id}, name is {name}, health is {health}, exp is {exp}, money is {money}. |

#### 一、数据范围与操作限制

##### 变量约束

| 变量                                                         | 类型   | 说明                     |
| ------------------------------------------------------------ | ------ | ------------------------ |
| id                                                           | 整数   | 取值范围：0 - 2147483647 |
| name                                                         | 字符串 | 保证不会出现空白字符     |
| price                                                        | 长整数 | 在 long 精度范围内       |
| capacity, efficiency, expRatio, sharpness, extraExpBonus, evolveRatio | 浮点数 | 在 double 精度范围内     |

##### 操作约束

* 操作数满足 $1 \leq m \leq 2000$​。
* 保证所有价值体的 ID 两两不同。
* 操作 1：不会加入与已有价值体 ID 相同 ID 的新冒险者。
* 操作 2：冒险者 ID 一定存在，且新装备的 ID 与当前所有价值体的 ID 均不相同。
* 操作 3：冒险者 ID 一定存在，且冒险者一定持有该 ID 的价值体。
* 操作 4：冒险者 ID 一定存在，若冒险者不持有任何价值体，则输出 0。
* 操作 5：冒险者 ID 一定存在，且冒险者一定持有至少一个价值体。
* 操作 6：冒险者 ID 一定存在，若冒险者不持有任何价值体，则输出 0。
* 操作 7：冒险者 ID 一定存在，且冒险者一定持有该 ID 的价值体。
* 操作 8：冒险者 ID 一定存在。
* 操作 9：冒险者 ID 一定存在。
* 操作 10：雇佣和被雇佣的冒险者均已存在，且不是同一个冒险者。
* 冒险者的雇佣关系不会存在循环雇佣的情况，每个冒险者最多仅能被一个其他冒险者雇佣一次。

#### 二、测评方法

输出数值时，你的输出数值需要和正确数值相等。

**假设你的输出值 $x_{out}$ 和正确数值 $x_{std}$ 之间的绝对或相对误差小于等于  $10 ^ {-5}$，则认为是相等的，即满足**

$$
\dfrac {|x_{std} - x_{out}|}{\max(1, |x_{std}|)} \leq 10^{-5}
$$

#### 三、输入样例

```
13
1 1 Saber 							
1 2 Lancer 							
1 114514 Ausar 						
2 1 1 3 bottle1 3 3 				
2 2 4 4 sword1 4 5 					
2 2 4 5 sword2 10 2 				
2 114514 1 6 bottle2 3 3 			
10 1 2 							
10 2 114514 							
7 1 2 							
4 1 								
6 1 								
8 1 							
```

#### 四、输出样例

```
The adventurer's id is 2, name is Lancer, health is 100.0, exp is 0.0, money is 0.0.
20
2
Saber used sword2 and earned 2.
Saber used sword1 and earned 5.
Saber drank bottle2 and recovered 0.3.
Saber drank bottle1 and recovered 0.3. 
```

----

### 第六部分：提示

冒险者和装备都是价值体，都可以**求价值**、**被使用**以及**字符串化**等，故一个推荐的设计方法是建立**价值体接口** ，接口中包含上述提到的三个方法，让冒险者 `Adventurer` 和装备 `Equipment` 都实现这个接口，这样在顶层逻辑中就只能看到**价值体**这一种类型，可使用该类型的引用去调用不同子类型对象的这三种方法，这种处理称为归一化处理，会在正式课程中有专门的论述和训练。



