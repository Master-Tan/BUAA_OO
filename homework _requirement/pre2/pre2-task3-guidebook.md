## 面向对象设计与构造预习作业2-3

### 第一部分：训练目标

>  学习继承，了解设计模式中的工厂模式

----

### 第二部分：预备知识

#### 一、继承

在接下来的任务中，你将学习到面向对象的基本特征之一——**继承**。

继承就是定义子类继承父类的特征和行为，使得子类可以拥有父类的属性和方法，从而起到代码复用的目的。

举个例子，假设我们有一个类 `Hero` 表示英雄，其包含生命值，保护盾值与魔法值这三个属性，并包含“徒手攻击”这一方法：

```java
public class Hero {
    int healthPoint;
    int defensePoint;
    int magicalPoint;
    
    public void attackWithHand() {
        /**/
    }
}
```

假设我们还想设计一个类，比如“骑士”类 `Knight` ，其也拥有生命，保护盾和魔法值，也拥有“徒手攻击”方法，除此之外其还拥有“手枪攻击”这个方法。如果从头开始实现这个类的话，需要编写如下代码：

```java
public class Knight {
    int healthPoint;
    int defensePoint;
    int magicalPoint;
    
    public void attackWithHand() {
        /**/
    }
    
    public void attackWithPistol() {
        /**/
    }
}
```

注意到骑士相比较英雄只多了一个使用手枪攻击的方法，其他部分都一样，所以我们可以认为骑士是一种特殊的英雄。其实我们还可能要设计“牧师“、“游侠”等类，其也拥有英雄类拥有的那些属性和方法，除此之外它们各自可能还有一些其他方法，则我们也可以将两个类也认为是特殊的英雄。倘若我们仍然直接编写代码，则又要写很多重复代码。如果直接复制粘贴，还要修改类名以及构造方法等地方，且假如第一个版本的方法写错了，后面复制粘贴的都会出错，修改时要处处做修改，非常麻烦。

这个时候，继承就登场了。使用继承，我们可以让类 `A` 去得到类 `B` 已有的属性和方法，接下来类 `A` 就只需要专注于编写其特有部分的代码了。

使用继承来编写骑士类的例子如下：

```java
public class Knight extends Hero {
    // 公共的属性和方法不需要重复编写
    
    // 只需要编写Knight特有的手枪攻击方法
    public void attackWithPistol() {
        /**/
    }
}
```

在Java中，我们使用 `extends` 关键字表示继承，`A extends B` 意味着 `A` 继承了 `B` ，`A` 是 `B` 的子类， `A` 得到了 `B` 的属性和方法。

#### 二、向上转型

在建立了继承关系之后，可以使用**父类型**去引用通过**子类型**创建的对象。

这里涉及两个重要的概念，对象与对象引用。一般而言，对象是一个类的实例化结果，对应内存中的一个数据结构。对象引用则是使用一个变量来指向内存中的这个数据结构（即对象）。没错，各位同学看着这个说法一定感觉似曾相识，这个对象引用本质上就是 C 语言中的指针，只不过，在 Java 程序中不能对这个对象引用实施 C 语言允许的指针运算。由这两个概念出发，我们需要进一步区分两个类型：对象类型和对象引用类型，前者有时又称为对象创建类型。需要注意的是，任何一个对象一旦创建，其对应的创建类型（即创建时调用的构造方法名对应的类）就一直保持不变（其实 Java 提供了获取该类型的手段，同学们不妨自行搜索一下）。对象引用类型则是指那个引用一个对象的变量的声明类型。

如我们可以使用上面的 Knight 类来构造一个对象：`new Knight()`，这条语句返回一个创建的对象。我们同时需要声明一个对象引用来指向返回的对象，否则可能就找不到这个对象了。所以，一般代码都会这么写：`Knight knt = new Knight()` 。

在建立了继承关系之后，我们也可以使用 Hero 类来声明一个对象引用，并指向类型为 Knight 的对象：`Hero h = new Knight()`。从程序类型的角度，这个表达方式称为向上的类型转换，简称**向上转型** (up cast)。向上转型的例子如下：

```java
public class Main {
    public static void main(String[] args) {
        Hero hero1 = new Knight();
        hero1.attackWithHand();
    }
}
```

因为 Knight 类提供了 `attackWithPistol()` 方法，因此通过 `new Knight()` 创建的对象是拥有手枪攻击这个能力。这里同学们可能会马上想到：能否通过上面例子中的 hero1 来调用这个方法呢？ 如下面的代码所示：

```java
public class Main {
    public static void main(String[] args) {
        Hero hero1 = new Knight();
        // 编译错误
        hero1.attackWithPistol();
    }
}
```

很不幸，上面的代码会出现编译错误，编译器认为 Hero 类中没有定义 `attackWithPistol()` 方法。这就带来了一个问题，明明所指向的对象拥有相应的方法，但是却不能调用。其原因是我们进行了向上转型，使用 Hero 类型的变量来引用它，这往往表明程序设计者此时只关心在 Hero 类这个层次能够看到的方法（否则就应该使用 Knight 来声明一个引用）。

#### 三、向下转型

对于3.1中出现的“父类型引用不能直接调用子类型对象特有的方法”的问题，细心的同学可能可以体会到为什么Java的设计为什么会出现这样的问题：倘若一个父类有多个子类，每个子类都有自己的特殊方法，假如父类引用真的能使用其引用的子类对象特有的方法，那么就可能出现调用了根本不存在的方法的问题。

在下面的例子中，我们让 `A` 是 `B` 和 `C` 的父类，`A` 拥有方法 `a()` ，`B` 和 `C` 拥有各自的方法 `b()` 和 `c()` ，然后执行下面的操作：

```java
public class Main {
    public static void main(String[] args) {
        // 开一个数组，这个数组里的所有引用是A类型的
        A[] list = new A[20];
        Scanner input = new Scanner(System.in);
        int cnt = 0;
        // 先构造10个对象，放到数组list中
        for (int i = 0; i < 10; i++) {
            int t = input.nextInt();
            if (t % 3 == 0) {
                list[cnt] = new A();
            } else if (t % 3 == 1) {
                list[cnt] = new B();
            } else {
                list[cnt] = new C();
            }
            cnt++;
        }
        // 我们想调用list中所有C类型对象的c()方法
        for (int i = 0; i < cnt; i++) {
            // c方法存在吗？
            list[i].c();
        }
    }
}

class A {
    public void a() {
        System.out.println("I am A");
    }
}

class B extends A {
    public void b() {
        System.out.println("I am B");
    }
}

class C extends A {
    public void c() {
        System.out.println("I am C");
    }
}
```

假设我们编写代码的编辑器没有代码联想功能，那么就很容易写出这样的代码。虽然这种错误在编译时就能被发现，但我们仍然可以设想一种情形：假设这段代码能通过编译，如果它可以正常工作，那么我们就不能在上述创建对象的过程中去创建 A 或者 B 的对象。所以，这种运行时才知道的信息导致 Java 在设计的时候就没想让父类型引用能直接使用其引用的子类型对象的特有方法，所以在编译的时候会把这种“父类型引用直接调用子类型对象特有的方法”当作是错误来处理。

还存在另外一种场景。现在存在一个有效的对象引用（即指向一个实际存在的对象），同时已知指向的对象的创建类型是对象引用类型的子类，而且此时想要调用子类特有的方法（即父类中不存在的方法），该如何处理？Java 语言提供了一个特殊的关键词 `instanceof` 用来判断一个对象引用所指向的对象的创建类型是否为特定的某个类，一般写为 `obj instanceof A`，其中 obj 为一个对象引用，A 为一个类型（类或接口），这个表达式的取值结果为布尔型，如果 obj 的创建类型为 A，则结果为 true，否则为 false。在这个表达式取值为 true 的情况下，可以使用**向下转型** (down cast) 来使用一个 A 类型的对象来引用obj： `A ao = (A)obj` 。注意，实际上 obj 所指向对象的创建类型永远不会发生变化，转型的只是对象引用类型。下面例子给出了相应的向下转型场景：

```java
public class Main {
    public static void main(String[] args) {
        A[] list = new A[20];
        Scanner input = new Scanner(System.in);
        int cnt = 0;
        // 先构造10个对象，放到数组list中
        for (int i = 0; i < 10; i++) {
            int t = input.nextInt();
            if (t % 3 == 0) {
                list[cnt] = new A();
            } else if (t % 3 == 1) {
                list[cnt] = new B();
            } else {
                list[cnt] = new C();
            }
            cnt++;
        }
        // 我们想调用list中所有C类型对象的c()方法
        for (int i = 0; i < cnt; i++) {
            // 先判断是不是C类型的对象，A instanceof B会返回true 或者 false
            if (list[i] instanceof C) {
                // 如果是，就向下转型，使用这个对象原本的类型的引用去指向它
                // 如果不是却还强行向下转型，则会出现错误
                C ref = (C) list[i];
                // 然后调用其c()方法
                ref.c();
            }
        }
    }
}
```

值得注意的是，在 `instanceof` 返回真的时候使用向下转型，才能保证向下转型的安全性，否则运行时会触发错误。

----

### 第三部分：基本要求

* 建立类 Equipment，所有的装备均继承自这个类（该类因而可称为基类, base class），请将所有装备都具有的属性定义在这个类里。
* 建立 Bottle 类与 Sword 类，应当满足
  * 符合某种继承关系
  * 具备信息查询方法
* 实现各项装备的查询和增删指令

具体实现细节将在“题目描述”中展开

----

### 第四部分：题目描述

现在我们将在上一个任务的基础上对 Bottle 进行细分，并添加新的“武器类”——Sword

| 药水类型      | 属性                                                         | 属性类型                                     |
| ------------- | ------------------------------------------------------------ | -------------------------------------------- |
| HealingPotion | 包括 Bottle 的全部属性，新增加属性 efficiency，代表药水的治疗效果 | Bottle 原有属性不变，efficiency 为浮点数类型 |
| ExpBottle     | 包括 Bottle 的全部属性，新增加属性 expRatio，代表水瓶对于经验值的增强效果 | Bottle 原有属性不变，expRatio为浮点数类型    |

| 武器类型  | 属性                                                         | 属性类型                                       |
| --------- | ------------------------------------------------------------ | ---------------------------------------------- |
| Sword     | sharpness，表示武器的锋利程度                                | sharpness 为浮点数类型                         |
| RareSword | 包括 Sword 的全部属性，新增加属性 extraExpBonus，代表使用武器的附加效果 | Sword 原有属性不变，extraExpBonus 为浮点数类型 |
| EpicSword | 包括 Sword 的全部属性，新增加属性 evolveRatio，代表使用武器的附加效果 | Sword 原有属性不变，evolveRatio 为浮点数类型   |

将有以下操作：

1. 加入一个冒险者
2. 给某个冒险者添加某件装备（装备包括药水和武器）
3. 删除某个冒险者拥有的某个装备
4. 查询某个冒险者所拥有装备的价格之和
5. 查询某个冒险者所拥有装备的价格最大值
6. 查询某个冒险者拥有的装备总数
7. 打印一个装备的全部属性，属性的输出顺序与输入创建该装备时给定的各参数顺序一致，具体格式详见下方`属性打印方式`

----

### 第五部分：输入输出

第一行一个整数 $m$，表示操作的个数。

接下来的 $m$ 行，每行一个形如 `{type} {attribute}` 的操作，操作输入形式及其含义如下：

| type | attribute                                                    | 意义                                                         | 输出文本                                   |
| ---- | ------------------------------------------------------------ | ------------------------------------------------------------ | ------------------------------------------ |
| 1    | `{adv_id} {name}`                                            | 加入一个 ID 为 `{adv_id}`、名字为 `{name}` 的冒险者，且未持有任何装备 | 无                                         |
| 2    | `{adv_id} {equipment_type} {vars}（equipment_type和vars的含义见下表）` | 给予某个人某件装备，装备类型由 `{equipment_type}` 定义，属性由 `{vars}` 定义，**所有的瓶子初始默认装满** | 无                                         |
| 3    | `{adv_id} {equipment_id}`                                    | 删除 ID 为 `{adv_id}` 的冒险者的 ID 为 `{equipment_id}` 的装备 | 无                                         |
| 4    | `{adv_id}`                                                   | 查询 ID 为 `{adv_id}` 的冒险者所持有装备的价格之和           | 一个整数，表示该冒险者所有装备的价格总和   |
| 5    | `{adv_id}`                                                   | 查询 ID 为 `{adv_id}` 的冒险者所持有装备价格的最大值         | 一个整数，表示该冒险者所有装备价格的最大值 |
| 6    | `{adv_id}`                                                   | 查询 ID 为 `{adv_id}` 的冒险者的装备总数                     | 一个整数，表示该冒险者所有装备的数量之和   |
| 7    | `{adv_id} {equipment_id}`                                    | 打印 ID 为 `{equipment_id}` 的装备的全部属性                 | 该装备的全部属性，格式见下文“属性打印方式” |

| 装备类型      | equipment_type | vars                                  |
| ------------- | -------------- | ------------------------------------- |
| Bottle        | 1              | id name price capacity                |
| HealingPotion | 2              | id name price capacity efficiency     |
| ExpBottle     | 3              | id name price capacity expRatio       |
| Sword         | 4              | id name price sharpness               |
| RareSword     | 5              | id name price sharpness extraExpBonus |
| EpicSword     | 6              | id name price sharpness evolveRatio   |

| 装备类型      | 属性打印方式                                                 |
| ------------- | ------------------------------------------------------------ |
| Bottle        | The bottle's id is {id}, name is {name}, capacity is {capacity}, filled is {filled}. |
| HealingPotion | The healingPotion's id is {id}, name is {name}, capacity is {capacity}, filled is {filled}, efficiency is {efficiency}. |
| ExpBottle     | The expBottle's id is {id}, name is {name}, capacity is {capacity}, filled is {filled}, expRatio is {expRatio}. |
| Sword         | The sword's id is {id}, name is {name}, sharpness is {sharpness}. |
| RareSword     | The rareSword's id is {id}, name is {name}, sharpness is {sharpness}, extraExpBonus is {extraExpBonus}. |
| EpicSword     | The epicSword's id is {id}, name is {name}, sharpness is {sharpness}, evolveRatio is {evolveRatio}. |

#### 数据范围与操作限制

##### 变量约束

| 变量                                                         | 类型   | 说明                     |
| ------------------------------------------------------------ | ------ | ------------------------ |
| id                                                           | 整数   | 取值范围：0 - 2147483647 |
| name                                                         | 字符串 | 保证不会出现空白字符     |
| price                                                        | 长整数 | 在 long 精度范围内       |
| capacity, efficiency, expRatio, sharpness, extraExpBonus, evolveRatio | 浮点数 | 在 double 精度范围内     |

##### 操作约束

* 操作数满足 $1 \leq m \leq 2000$​。
* 保证所有冒险者与装备的 ID 两两不同。
* 操作 1：不会加入与已有冒险者和装备 ID 相同 ID 的新冒险者。
* 操作 2：冒险者 ID 一定存在，且新装备的 ID 与当前所有冒险者和装备的 ID 均不相同。
* 操作 3：冒险者 ID 一定存在，且冒险者一定持有该 ID 的装备。
* 操作 4：冒险者 ID 一定存在，若冒险者不持有任何装备，则输出 0。
* 操作 5：冒险者 ID 一定存在，且冒险者一定持有至少一个装备。
* 操作 6：冒险者 ID 一定存在，若冒险者不持有任何装备，则输出 0。
* 操作 7：冒险者 ID 一定存在，且冒险者一定持有该 ID 的装备。

#### 测评方法

输出数值时，你的输出数值需要和正确数值相等。

**假设你的输出值 $x_{out}$ 和正确数值 $x_{std}$ 之间的绝对或相对误差小于等于  $10 ^ {-5}$，则认为是相等的，即满足**

$$
\dfrac {|x_{std} - x_{out}|}{\max(1, |x_{std}|)} \leq 10^{-5}
$$

#### 输入样例

```
9
1 1 Person1
1 2 Person2
2 1 1 3 bottle1 10 5
2 1 6 4 sword1 20 7 0.6
2 2 3 5 bottle2 15 3 8
6 1
7 2 5
3 1 3
5 1
```

#### 输出样例

```
2
The expBottle's id is 5, name is bottle2, capacity is 3.0, filled is true, expRatio is 8.0.
20
```

----

### 第六部分：补充材料

1. 请思考，本次作业中的**求和**操作等是否会出现超出数据限制的情况。

   提示：Java 中有特别的类：`BigInteger` 和 `BigDecimal` 。

2. **设计模式**是软件开发人员经过相当长的实践总结出来的最佳设计方案，在面向对象设计与构造课程中，你将逐步了解和掌握几种基本的设计模式，包括工厂模式、单例模式、生产者-消费者模式等。

   现在，希望大家可以了解**工厂模式**，这是在继承和接口实现中常用的设计模式。

   大家可以参考[链接](https://www.runoob.com/design-pattern/factory-pattern.html)中的介绍，也可以自行查阅资料。这将帮助你更轻松的完成日后的作业 :)