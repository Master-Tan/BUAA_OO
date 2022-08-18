## 面向对象设计与构造预习作业2-4

### 第一部分：训练目标

学习方法的重写、Java 的多态机制以及 Java 的异常处理机制，学会使用 Java 类库提供的类进行排序。

----

### 第二部分：预备知识

#### 一、对象方法的重写和复用

有时候，你会发现具有继承关系的类的某些行为具有递进关系，比如在下方代码中 Course类 和 OOCourse类 之间具有继承关系，OOCourse与Course有部分**相同**行为（即Course中定义且被OOCourse继承的行为），但OOCourse也会有自己的**特有**行为。为了保持OOCourse与Course的整体一致性，我们期望OOCourse中实现了特有行为的方法名与Course中实现相应行为的方法同名，这样可以确保在任何时候不论是使用Course对象引用，或者OOCourse对象引用来访问OOCourse对象时都能够顺利调用相应的方法。这种让子类重新实现一个在父类中已经实现的方法是面向对象的一个重要机制，称为方法重写。方法重写获得的直接好处是让子类与父类在相应方法的调用上保持了一致性。

更通俗的说，重写方法与父类方法在行为上具有相似功能，但子类重写的方法一般额外增加一些行为。举例而言，设Course中实现了一个显示课程信息的方法(displayInfo)，我们希望OOCourse重新实现这个方法，从而能够多显示一些特有的信息。在程序编写方面，一般会标上一个@Override标签，便于开发人员了解一个方法是否为重写方法。在重写机制下，不论你使用Course类型的引用来访问一个对象，或者使用OOCourse类型的引用来访问，当调用其displayInfo方法时，具体调用的是父类的方法，还是子类重写的方法，就变成了一个需要梳理清楚的关键问题。在回答这个问题之前，首先看下面的例子： 


```java
class Course {
    void displayInfo() {
        System.out.println("老师上课，同学完成作业，最终老师会给一个成绩");
    }
}
```

```java
class OOCourse extends Course {
    @Override
    void displayInfo() {
        System.out.println("老师上课，同学完成作业，最终老师会给一个成绩");
        System.out.println("还有研讨课，强测互测等任务，学期结束还会有颁奖典礼");
    }
}
```

我们可以看到OOCourse重写的信息显示方法中的第一句话与Course中信息显示方法的语句完全相同，这实质上就是重写方法与父类相应方法之间的相同行为。通常，我们不希望出现重复编写代码（又称为代码拷贝）的现象，那样不便于维护代码（试想一旦Course的displayInfo方法实现进行修改，还需要对OOCourse相应方法的相应语句进行修改，很是繁琐）。Java语言提供了一个重要的关键词super，它实际指代的是当前对象从父类继承得到的内容，因此通过super.displayInfo()可以确保调用的是Course实现的displayInfo方法。请看下面的例子， OOCourseAlpha 和 OOCourse 具有完全相同的行为，但从面向对象角度， OOCourseAlpha 的实现方式更好，更便于维护代码。

```java
class OOCourseAlpha extends Course {
    @Override
    void displayInfo() {
        super.displayInfo(); // 调用了类Course中定义的方法
        System.out.println("还有研讨课，强测互测等任务，学期结束还会有颁奖典礼");
    }
}
```

你可能会质疑、明明可以只写一个OOCourse类就完成想要的功能，为什么非要用Course和OOCourseAlpha两个类还要写继承关系，明明这样我写了更多的代码？？？答案是，如果你还需要编写其他的课程类，比如COCourse和OSCourse，那么通过继承共用Course类的代码就可以省下一些力气。如果你只单单只想写一个OOCourse类，那么或许可能只写一个反而是更好的。

#### 二、多态

前面提到，如何判断实际调用的是子类重写的方法，还是父类实现的方法。其实，这与对象**引用的类型**无关，而是取决于被引用对象的**创建类型**。请看下面的代码示例：

```java
Course c1 = new Course();
Course c2 = new OOCourseAlpha();
c1.displayInfo();
c2.displayInfo();
```

其中通过c1调用的实际是Course类实现的displayInfo方法，而通过c2调用的则是OOCourseAlpla类重写的displayInfo方法，但实际上c1和c2的引用类型都是Course。
上面我们提到的这个特性，就叫做多态。

#### 三、异常处理

什么是异常？

程序运行时，发生了不被期望的事件，它阻止了程序按照程序员的预期正常执行，这就是异常。

在 C 语言中，我们通常让函数返回明显区别于正常处理的值（如对于从输入的数组中查询最大值所在的位置，如果输入的数组指针为空，则返回负数）来代表函数执行期间发生了异常。这种通过特殊返回值的异常处理方式，是一种隐含的方式，很容易被人忽略，导致在调用一个函数时忽略掉特殊返回值的情形，从而导致出错。相对而言，Java 提供了更加优秀的解决办法：异常处理机制。

异常处理机制采取显式的方式来处理异常，包括两个方面：（1）引入了专门的表达和处理方式，代码上一目了然就能看出是异常处理；（2）一旦发生异常，会强迫程序执行进入异常处理分支，不会让异常“暗度陈仓”。在Java语言中，每个异常都被封装为Exception，当然程序员可以对Exception进行扩展（通过继承）来定义特定的异常。异常有抛出和捕捉两种处理方式。所谓抛出，就是使用Java提供的throw关键词来产生一个Exception或者其某个子类的对象；而捕捉则是通过catch关键词来捕捉在一段代码的执行过程中所抛出的相关异常对象。

课程推荐使用异常处理机制来区分处理显著不同于一般情况下的数据状态。使用异常处理可以让你的代码更加清晰易于理解，降低出现 bug 的可能性。请阅读《Core Java》的第七章相关内容了解异常处理机制的使用方法，并参照本章最后 Tips 部分来使用异常处理优化你的代码。

----

### 第三部分：题目描述

* 冒险者除了具有 id, 姓名 name, 拥有的装备 equipment 等状态外，还增加了另外的一些属性：生命值 （`health`, 浮点数，默认值 100.0）、经验值（ `exp`, 浮点数，默认 0.0）、金钱数（ `money`, 浮点数，默认 0.0）。
* 每一种装备都有一个**使用**方法，定义如下，设冒险者A使用了装备B：

| 装备B的类型                                       | 使用效果                                                     | 输出文本                                                     |
| ------------------------------------------------- | ------------------------------------------------------------ | ------------------------------------------------------------ |
| Bottle（若 filled 为 true）                       | A的生命值增加[B的 capacity 属性]的十分之一，之后 B 的 filled 变为 false，price 变为原来的十分之一（向下取整）。 | {A 的 name} drank {B 的 name} and recovered {生命值增加量}.  |
| HealingPotion（若 filled为true）                  | A的生命值增加[B的 capacity 属性]的十分之一，之后 B 的 filled 变为 false，price 变为原来的十分之一（向下取整）。然后A的生命值再额外增加[B的capacity属性]乘以[B的efficiency属性]的量。 | {A 的 name} drank {B 的 name} and recovered {生命值增加量}.<br />{A 的 name} recovered extra {生命值额外增加量}. |
| ExpBottle（若 filled 为 true）                    | A的生命值增加[B的 capacity 属性]的十分之一，之后 B 的 filled 变为 false，price 变为原来的十分之一（向下取整）。然后A的经验值变为原来的[B的expRatio属性]倍。 | {A 的 name} drank {B 的 name} and recovered {生命值增加量}.<br />{A 的 name}'s exp became {A 变化后的经验}. |
| Bottle/HealingPotion/ExpBottle（若filled为false） | 无任何作用效果。                                             | Failed to use {B 的 name} because it is empty.               |
| Sword                                             | 使用后A的生命值减少 10.0、经验值增加 10.0，金钱数增加相当于[B 的 sharpness属性]一倍的量。 | {A 的 name} used {B 的 name} and earned {增加的金钱数}.      |
| RareSword                                         | 使用后A的生命值减少 10.0、经验值增加 10.0，金钱数增加相当于[B 的 sharpness属性]一倍的量。然后 A 的经验值额外增加[B 的 extraExpBonus 属性]。 | {A 的name} used {B 的name} and earned {增加的金钱数}.<br />{A 的name} got extra exp {额外获得的经验}. |
| EpicSword                                         | 使用后A的生命值减少 10.0、经验值增加 10.0，金钱数增加相当于[B 的 sharpness属性]一倍的量。然后B的sharpness 属性变为原来的 evolveRatio倍。 | {A 的 name} used {B 的 name} and earned {增加的金钱数}.<br />{B 的 name}'s sharpness became {B 变化后的sharpness}. |

请注意打印文本中存在的换行。

----

### 第四部分：输入/输出格式

第一行一个整数 $m$，表示操作的个数。

接下来的 $m$ 行，每行一个形如 `{type} {attribute}` 的操作，操作输入形式及其含义如下：

* 指令相较于 task3 增加两条，其余指令不发生变化。

| type | attribute  | 意义                                                         | 输出文本                                                     |
| ---- | ---------- | ------------------------------------------------------------ | ------------------------------------------------------------ |
| 8    | `{adv_id}` | 编号为 `{adv_id}` 的冒险者按照 `price` 由大到小的顺序使用其全部装备，若 `price` 相同则按照装备的 `id` 由大到小使用。（ `price` 为所有装备本次使用前的 `price` ） | 每个装备在使用时会产生输出，除此之外无额外输出。             |
| 9    | `{adv_id}` | 打印编号为 `{adv_id}` 的冒险者的所有状态。                   | 一个字符串表示冒险者的状态：<br />The adventurer's id is {adv_id}, name is {name}, health is {health}, exp is {exp}, money is {money}. |

#### 数据范围与操作限制

##### 变量约束

| 变量                                                         | 类型   | 说明                     |
| ------------------------------------------------------------ | ------ | ------------------------ |
| id                                                           | 整数   | 取值范围：0 - 2147483647 |
| name                                                         | 字符串 | 保证不会出现空白字符     |
| price                                                        | 长整数 | 在 long 精度范围内       |
| capacity, efficiency, expRatio, sharpness, extraExpBonus, evolveRatio | 浮点数 | 在 double 精度范围内     |

##### 操作约束

* 操作数满足 $1 \leq m \leq 2000$。
* 保证所有冒险者与装备的 ID 两两不同。
* 操作 1：不会加入与已有冒险者和装备 ID 相同 ID 的新冒险者。
* 操作 2：冒险者 ID 一定存在，且新装备的 ID 与当前所有冒险者和装备的 ID 均不相同。
* 操作 3：冒险者 ID 一定存在，且冒险者一定持有该 ID 的装备。
* 操作 4：冒险者 ID 一定存在，若冒险者不持有任何装备，则输出 0。
* 操作 5：冒险者 ID 一定存在，且冒险者一定持有至少一个装备。
* 操作 6：冒险者 ID 一定存在，若冒险者不持有任何装备，则输出 0。
* 操作 7：冒险者 ID 一定存在，且冒险者一定持有该 ID 的装备。
* 操作 8：冒险者 ID 一定存在。
* 操作 9：冒险者 ID 一定存在。

#### 测评方法

输出数值时，你的输出数值需要和正确数值相等。

**假设你的输出值 $x_{out}$ 和正确数值 $x_{std}$ 之间的绝对或相对误差小于等于  $10 ^ {-5}$，则认为是相等的，即满足**

$$
\dfrac {|x_{std} - x_{out}|}{\max(1, |x_{std}|)} \leq 10^{-5}
$$

#### 输入样例

```
6
1 1 Person1
2 1 1 2 water_bottle1 10 50.0
2 1 6 3 epic_sword1 300 7.0 1.5
2 1 3 4 exp_bottle1 10 3.0 1.2
8 1
9 1
```

#### 输出样例

```
Person1 used epic_sword1 and earned 7.0.
epic_sword1's sharpness became 10.5.
Person1 drank exp_bottle1 and recovered 0.3.
Person1's exp became 12.0.
Person1 drank water_bottle1 and recovered 5.0.
The adventurer's id is 1, name is Person1, health is 95.3, exp is 12.0, money is 7.0.
```

----

### 第五部分：提示

1. 建议在Equipment类中定义一个use方法，在所有的装备子类中都去重写这个use方法，另外还应该为所有需要打印描述字符串的类重写toString方法。在Adventurer类中定义`HashMap<Integer, Equipment>`类型的equipments属性，表示冒险者拥有的全部装备，在执行操作8时，先对equipments中存储的装备进行排序，然后依次调用这些装备对象的use方法（因为有多态机制，这里不需要强制转型，直接调用就可以保证行为正确）。
2. 冒险者使用装备的过程中，是对冒险者属性和装备自身属性的读取，运算和修改。如何才能让装备类的方法可以读取并修改他的使用者的属性呢？为`use`方法传递一个冒险者作为参数是一个好主意。
3. 在 `Bottle` 和它的子类在 `filled` 为 `false` 时被使用就可以看作是一种异常行为。于是你可以在 `Bottle.use` 方法中抛出一个异常（使用 throw 语句），在 `HealingPotion.use` 调用 `Bottle.use` 时，不处理这个异常而是将其继续抛出到上层，而在冒险者循环使用装备的代码中将其捕获并打印出错误信息。

下面的代码是标程中Bottle类内定义的use方法。

```java
@Override
public void use(Adventurer user) throws Exception {
    if (!isFilled()) {
        throw new Exception("Failed to use " + getName() + " because it is empty.");
    }
    user.setHealth(user.getHealth() + capacity / 10);
    setFilled(false);
    setPrice(getPrice().divide(BigInteger.TEN));

    System.out.println(user.getName() +
            " drank " + getName() +
            " and recovered " + capacity / 10 +
            ".");
}
```

下面的代码是标程中在Adventurer类中用于完成操作8所定义的useAll方法

```java
public void useAll() {
    ArrayList<Equipment> sorted = new ArrayList<>(equipments.values());
    Collections.sort(sorted, Comparator.reverseOrder());
    for (Equipment equipment : sorted) {
        try {
            equipment.use(this);
        } catch (Exception e) {
            System.out.println(e.getMessage());
        }
    }
}
```

4. 本次作业将会涉及到自定义排序，请学习如何给对象编写 `compareTo` 方法并实现 `Comparable` 接口，之后即可利用 `Collections.sort` 方法来给容器内对象进行排序，考虑到有许多知识同学们还没有学过，本章结尾会给出一个例子，同学们可以照猫画虎地完成，compareTo方法仅需要在Equipment类中定义，Equipment类的子类如果不重写该方法的话，将会与父类行为保持一致。

> 与 `Collections.sort` 会调用 `compareTo` 方法实现自定义排序，类似地，`TreeSet` 和 `TreeMap` 容器也会通过调用对象的 `compareTo` 方法，从而维护一个key对象有序的集合/映射。
>
> 另外，`HashSet` 和 `HashMap` 这两种容器会通过调用对象的 `hashCode` 方法和 `equals` 方法来将任意对象作为key来使用。**这个知识点非常重要，请同学们务必弄懂其原理**。
>
> Java中许多内置的类，比如 `Integer` 和 `BigInteger` 等等都已经实现了`compareTo`、`hashCode`、`equals` 方法，所以你才可以直接把他们当作 `TreeMap` 和 `HashMap` 的key来使用。




```java
// Comparable接口的例子

import java.util.ArrayList;
import java.util.Collections;

class MainClass {
    public static void main(String[] args) {
        Score xiaoMing = new Score(120, 138);
        Score xiaoHong = new Score(125, 133);
        Score xiaoWang = new Score(119, 145);
        ArrayList<Score> scores = new ArrayList<>();
        scores.add(xiaoMing);
        scores.add(xiaoHong);
        scores.add(xiaoWang);

        Collections.sort(scores);

        for (Score score : scores) { // 如果你使用IDEA编写代码，可以试一试打出 "scores.for<TAB>" 这一串按键，快速补齐for循环
            System.out.println(score); // 试一试 "score.sout<TAB>"，自动补齐打印语句
        }
        /*
        运行结果如下，越大的对象越在后面（即升序排序）:
        Score{chinese=120, math=138}
        Score{chinese=125, math=133}
        Score{chinese=119, math=145}
         */
    }
}

class Score implements Comparable<Score> { // 后面尖括号里的类名基本上都会与前面的类名相同，表达“Score这个类可以与Score这个类相比较”这个意思。
    private final int chinese;
    private final int math;

    public Score(int chinese, int math) {
        this.chinese = chinese;
        this.math = math;
    }

    public int getSum() {
        return chinese + math;
    }

    /**
     * 自定义分数的比较规则，首先比较总分，总分相同比较语文，语文相同比较数学……
     */
    @Override
    public int compareTo(Score other) {
        if (this.getSum() < other.getSum()) { //首先比较总分，总分高的先录取
            return -1; // 返回 -1 代表 this 小于 other
        } else if (this.getSum() > other.getSum()) {
            return 1; // 返回 1 代表 this 大于 other
        }

        if (this.chinese < other.chinese) { //若总分一样，按语文分更高的先录取
            return -1;
        } else if (this.chinese > other.chinese) {
            return 1;
        }

        // 返回任何负值都代表this < other，于是可以这样子简写，
        // 下面三行关于math的比较和上面的五行关于chinese的比较是完全等价的。
        if (this.math != other.math) {
            return this.math - other.math; 
        }

        return 0; //返回0代表两被比较对象相等
    }

    @Override
    public String toString() {
        return "Score{" +
                "chinese=" + chinese +
                ", math=" + math +
                '}';
    }

}
```

