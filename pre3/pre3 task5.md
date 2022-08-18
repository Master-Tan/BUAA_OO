## 面向对象设计与构造预习作业3-5

### 第一部分：训练目标

本task希望同学们了解UML类图相关基础知识。UML类图将有效帮助你分析代码的整体结构，也可以帮助你以简明扼要的方式展现自己的架构设计。不论是在团队的合作交流，还是在分析设计的过程中，都将为你提供便利。我们将在课程第四单元来重点学习基于UML的分析与设计。

UML类图是UML的模型图中最基本也最重要的内容，我们希望你能通过预习课程，对UML类图有初步了解，学会用UML类图分析和讲述设计架构，这将有利于你在第一单元中理清层次化设计思路。

----


### 第二部分：工具

绘制UML图利器：starUML，可以在课程提供的北航云盘中下载安装包，也可以自行从网络下载更新的版本。

----

### 第三部分：基础知识

#### UML类图

类图中常见的元素可以分成两类，节点和连线（关系）。节点主要包括类和接口，而连线主要包括泛化、关联、聚集、实现。

##### 类

在类图中，一个类的完整表示包括三部分：名称、属性和方法，其中每个属性的表示包括属性名、属性类型和属性的可见性，方法的表示包括方法名、方法参数、方法的返回值类型、方法的可见性，而每个参数都应该按照参数名和参数类型来规范表示。

###### 示例

```java
public abstract class Vehicle {
    private int id;
    private int price;

    Vehicle(int id, int price) {
        this.id = id;
        this.price = price;
    }

    public abstract void run();
    
    public int getPrice() {
        return price;
    }
}
```

这个代码中Vehicle类包含两个属性：`id`、`price`，以四个方法`run`、`getPrice`。

它的类图长这样：

![1](E:\OOProject-Star\2021_oo_course\pre\pre3\指导书\pics\1.PNG)

##### 接口

###### 示例

```java
public interface Manned {
    void getIn(int newPassenger);
    void getOff();
}
```



##### 关系

+ **泛化(Generalization)**
  + 【泛化关系】是一种继承关系，表示子类继承父类的所有特征和行为
  + 【箭头指向】带三角箭头的**实线**，**箭头指向父类**
  + ![4](E:\OOProject-Star\2021_oo_course\pre\pre3\指导书\pics\4.PNG)

+ **实现(Realization)**
  + 【实现关系】是一种类与接口的关系，表示类实现了一个接口所定义的所有行为
  + 【箭头指向】带三角箭头的**虚线**，**箭头指向接口**
  + ![5](E:\OOProject-Star\2021_oo_course\pre\pre3\指导书\pics\5.PNG)

###### 示例

我们知道一个类可能会继承其他类，也可能会实现一些接口，这些信息也需要在类图中有所体现，请看下面这个例子。

```java
public class Bus extends Vehicle implements Manned, Engineered {
    private int volume;
    private int passenger;

    public Bus(int id, int price, int volume) {
        super(id, price);
        this.volume = volume;
    }

    @Override
    public void run() {
        System.out.println("Wow, I can Run all day!");
    }

    @Override
    public void work() {
        System.out.println("Working!" + " " + this.volume + "L diesel oil used!");
    }

    @Override
    public void getIn(int newPassenger) {
        passenger = passenger + newPassenger;
        System.out.println("Wow! We have a new passenger!");
    }

    @Override
    public void getOff() {
        if (passenger <= 0) {
            System.out.println("Wow! Only Driver!");
        } else {
            passenger = passenger - 1;
            System.out.println("Wow! A passenger arrived at his or her destination!");
        }
    }
}

```

Bus这个类继承了`Vehicle`类，并且实现了`Manned`和`Engineered`两个接口。如果我们将上述的`Bus`、`Manned`、`Vehicle`汇总到一起，就构成了一个简单的类图。这个图包含了代码中的属性、方法，也展示出了不同类（或接口）的关系。

![7](E:\OOProject-Star\2021_oo_course\pre\pre3\指导书\pics\7.PNG)



----

### 第四部分：小测

在一些作业中，课程中设计了小测模块来提示大家关注到指导书中的一些细节内容，帮助同学更好地理解知识点或题目意图，以减少由于理解不当而造成的代码重构现象。因而，希望各位同学在完成小测题目后，再动手写代码。在小测提交后，才可以进入作业的评测板块，正式提交作业。

- 请阅读给出的task_5代码（见gitlab仓库）和它的类图，回答以下问题。

  > 这段代码描述了一个简单的**工厂模式**的例子，这种设计思路，将对你第一单元的学习有所帮助。

![6](E:\OOProject-Star\2021_oo_course\pre\pre3\指导书\pics\6.PNG)

  1. 与`Vehicle`抽象类有泛化关系的类有Car、Sprinkler、_\_

  2. 请阅读`Factory`部分代码和UML图，回答以下问题：

     `Factory`类的`getNew`方法的功能是按照需求创造出合适类型的车，规定返回值的类型为__，但是事实上，在代码实现中，我们可以根据要求的不同，返回对应的`Vehicle`的一个子类的对象，这样我们就可以通过一个`getNew`创造出不同类型的车。

  3. 请阅读`Vehicle`和`Main`代码和UML图，回答以下问题：

     在`Main`中，不论是`Bus`、`Car`还是`Sprinker`，我们都可以将其看成`Vehicle`，直接调用`Vehicle`中的run、getPrice方法，然而其中的\_\_方法在`Vehicle`中并没有真正实现这一方法，而是在其各子类中以不同的方式实现。

  4. 由于实现了`Manned`，Bus类必须实现`Manned`所要求的方法_\_、\_\_，因而，我们不需要查看代码，即可知它拥有这一方法。

  5. 阅读`Bus`、`Sprinker`部分代码和UML图，回答以下问题：

     虽然都实现了`Engineered`接口，但是，这两个类对于`Engineered`中要求的`work`方法的实现可以有所不同，其中`Bus`执行语句为`System.out.println("Working!" + " " + this.volume + "L diesel oil used!");`，而`Sprinker`执行语句为`System.out.println(__);`(请复制对应代码)

----

### 第五部分：提交方法

请将你的pre2_task5的代码画成UML**类图**（`.mdj`文件，在根目录中）和该类图所对应的**代码**，提交至本次作业对应的仓库中。

在绘制类图时，我们希望同学们能进一步梳理原先的代码，因而我们**允许**本次提交的代码与pre2_task5中提交的代码有所不同，但需要注意的是，类图必须与**本次**代码相符。

由于同学们刚刚接触面向对象的思想，我们对类图的要求将适当放宽。类图中仅需展示本次task指导书中所介绍的元素（类、接口）和关系（继承、泛化）即可，学有余力的同学可以思考添加更多种类的元素与关系。

本次作业仅有一个数据点，与pre2_task5的weak1数据点相同。成功提交并通过该测试点即认为本次task通过，在pre结束后，我们将对类图进行人工复核，选取优秀的设计架构进行展示，以帮助同学们更好地学习和掌握面向对象相关思想。

----

### 第六部分：提示

在UML类图中除了泛化与实现，还有关联和组合等关系，随着学习的深入，我们将逐步理解这些关系在架构设计中的特点。

除了类图，UML还有时序图、状态图等，在面向对象课程的学习过程中，希望你能了解并使用这些图来帮助你进行设计与分析。