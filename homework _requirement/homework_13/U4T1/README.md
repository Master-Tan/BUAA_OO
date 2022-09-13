# UML 第一次作业接口使用说明

本次我们继续像是之前一样，提供封装好的 jar 包给大家。

这次的话，**我们已经将全部的主干业务逻辑进行了封装，只需要同学们实现一个核心交互类即可**。

除此之外，本次的**官方包还可以作为命令行工具使用，以便快速从`mdj`文件中导出并生成输入数据**。

## 功能实现

### UserApi 接口

学生需要实现一个自己的`MyImplementation`类，这个类必须继承接口`com.oocourse.uml1.interact.format.UserApi`。

```java
import com.oocourse.uml1.interact.format.UserApi;

public class MyImplementation implements UserApi {
    // TODO : IMPLEMENT
}
```

接口源码设定：

```java
package com.oocourse.uml1.interact.format;

import com.oocourse.uml1.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml1.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml1.interact.exceptions.user.MethodDuplicatedException;
import com.oocourse.uml1.interact.exceptions.user.MethodWrongTypeException;
import com.oocourse.uml1.models.common.Visibility;

import java.util.List;
import java.util.Map;

/**
 * UML交互接口
 */
@SuppressWarnings("unused")
public interface UserApi {
    /**
     * 获取类数量
     * 指令：CLASS_COUNT
     *
     * @return 类数量
     */
    int getClassCount();

    /**
     * 获取类的子类数量
     * 指令：CLASS_SUBCLASS_COUNT
     *
     * @param className 类名
     * @return 直接继承该类的子类数量
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    int getClassSubClassCount(String className)
            throws ClassNotFoundException, ClassDuplicatedException;


    /**
     * 获取类操作数量
     * 指令：CLASS_OPERATION_COUNT
     *
     * @param className 类名
     * @return 类的操作数量
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    int getClassOperationCount(String className)
            throws ClassNotFoundException, ClassDuplicatedException;

    /**
     * 统计类操作可见性
     * 指令：CLASS_OPERATION_VISIBILITY
     *
     * @param className     类名
     * @param methodName 操作名
     * @return 类操作可见性统计结果
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    Map<Visibility, Integer> getClassOperationVisibility(String className, String methodName)
            throws ClassNotFoundException, ClassDuplicatedException;

    /**
     * 查询类的操作的耦合度
     * 指令：CLASS_OPERATION_COUPLING_DEGREE
     *
     * @param className     类名
     * @param methodName 操作名
     * @return 类的操作的耦合度
     * @throws ClassNotFoundException    类未找到异常
     * @throws ClassDuplicatedException  类重复异常
     * @throws MethodWrongTypeException  存在错误类型
     * @throws MethodDuplicatedException 存在重复操作
     */
    List<Integer> getClassOperationCouplingDegree(String className, String methodName)
            throws ClassNotFoundException, ClassDuplicatedException,
            MethodWrongTypeException, MethodDuplicatedException;

    /**
     * 查询类的属性的耦合度
     * 指令：CLASS_ATTR_COUPLING_DEGREE
     *
     * @param className 类名
     * @return 类的属性的耦合度
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    int getClassAttributeCouplingDegree(String className)
            throws ClassNotFoundException, ClassDuplicatedException;


    /**
     * 获取实现的接口列表
     * 指令：CLASS_IMPLEMENT_INTERFACE_LIST
     *
     * @param className 类名
     * @return 实现的接口列表
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    List<String> getClassImplementInterfaceList(String className)
            throws ClassNotFoundException, ClassDuplicatedException;

    /**
     * 获取类的继承深度
     * 指令：CLASS_DEPTH_OF_INHERITANCE
     *
     * @param className 类名
     * @return 类的继承深度
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    int getClassDepthOfInheritance(String className)
            throws ClassNotFoundException, ClassDuplicatedException;

}

```

除此之外，`UserApi`类必须实现一个构造方法

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

构造函数的逻辑为将`elements`数组内的各个 UML 类图元素传入`MyImplementation`类，以备后续解析。

### 交互模式

交互的模式为：

- 调用上述构造函数，生成一个实例，并将 UML 模型元素传入。
- 之后将调用此实例的各个接口方法，以实现基于之前传入的 UML 模型元素的各类查询操作。
- 官方接口通过调用方法的返回值，自动生成对应的输出文本。

### 开始运行

运行的模式和之前基本类似：

```java
import com.oocourse.uml1.interact.AppRunner;

public class Main {
    public static void main(String[] args) throws Exception {
        AppRunner appRunner = AppRunner.newInstance(MyImplementation.class);
        appRunner.run(args);
    }
}
```

将自己实现的类进行载入，即可运行。

## 数据生成

### 命令行工具

和之前不同的是，此次的官方 jar 包还可以作为命令行工具使用，简单的几个用法如下。

#### 查看可导出的数据模型列表

用户可以通过这一功能查看支持导出的数据模型列表

```bash
java -jar uml-homework.jar list -s "open-close.mdj"
```

输出结果

```text
|   Name   |    Type    |
|----------|------------|
| Model    | UMLModel   |
| Model1   | UMLModel   |
```

#### 导出指定的数据模型

用户可以通过这一功能对数据模型进行导出。

导出的数据格式可以直接作为数据模型的输入内容，在其后接上`END_OF_MODEL`和各类指令，即可构建为一个输入数据。

```bash
java -jar uml-homework.jar dump -s "open-close.mdj" -n Model1
```

输出结果

```json
{"_parent":"AAAAAAFq3tvYM76UevI=","visibility":"public","name":"Key","_type":"UMLClass","_id":"AAAAAAFq7weIMSb5xqQ="}
{"_parent":"AAAAAAFq7weIMSb5xqQ=","visibility":"public","name":"equals","_type":"UMLOperation","_id":"AAAAAAFq7weIMSb8qxc="}
{"_parent":"AAAAAAFq7weIMSb8qxc=","name":"o","_type":"UMLParameter","_id":"AAAAAAFq7weIMSb9G0k=","type":"Object","direction":"in"}
{"_parent":"AAAAAAFq7weIMSb8qxc=","name":null,"_type":"UMLParameter","_id":"AAAAAAFq7weIMSb+Au4=","type":"boolean","direction":"return"}
{"_parent":"AAAAAAFq7weIMSb5xqQ=","visibility":"public","name":"getMatchedLockId","_type":"UMLOperation","_id":"AAAAAAFq7weIMSb\/6gM="}
{"_parent":"AAAAAAFq7weIMSb\/6gM=","name":null,"_type":"UMLParameter","_id":"AAAAAAFq7weIMScAoOk=","type":"int","direction":"return"}
{"_parent":"AAAAAAFq7weIMSb5xqQ=","visibility":"public","name":"Operation1","_type":"UMLOperation","_id":"AAAAAAFq7w1zLCePJrI="}
{"_parent":"AAAAAAFq7w1zLCePJrI=","name":"Parameter1","_type":"UMLParameter","_id":"AAAAAAFq7w2dZCeV4K8=","type":{"$ref":"AAAAAAFq7weIMSb5xqQ="},"direction":"return"}
{"_parent":"AAAAAAFq7weIMSb5xqQ=","name":null,"_type":"UMLGeneralization","_id":"AAAAAAFq7wfNvyd+GgY=","source":"AAAAAAFq7weIMSb5xqQ=","target":"AAAAAAFq7weqoCcQE7I="}
{"_parent":"AAAAAAFq7weIMSb5xqQ=","visibility":"private","name":"keyID","_type":"UMLAttribute","_id":"AAAAAAFq7weIMSb6+v8=","type":"int"}
{"_parent":"AAAAAAFq7weIMSb5xqQ=","visibility":"private","name":"matchedLockID","_type":"UMLAttribute","_id":"AAAAAAFq7weIMSb7oPM=","type":"int"}
{"_parent":"AAAAAAFq3tvYM76UevI=","visibility":"public","name":"ElcKey","_type":"UMLClass","_id":"AAAAAAFq7weqoCcQE7I="}
{"_parent":"AAAAAAFq7weqoCcQE7I=","visibility":"public","name":"equals","_type":"UMLOperation","_id":"AAAAAAFq7weqoCcTngY="}
{"_parent":"AAAAAAFq7weqoCcTngY=","name":"o","_type":"UMLParameter","_id":"AAAAAAFq7weqoCcUI6g=","type":"Object","direction":"in"}
{"_parent":"AAAAAAFq7weqoCcTngY=","name":null,"_type":"UMLParameter","_id":"AAAAAAFq7weqoCcVxI0=","type":"boolean","direction":"return"}
{"_parent":"AAAAAAFq7weqoCcQE7I=","name":"sdfsdf","_type":"UMLGeneralization","_id":"AAAAAAFq7weqoCcRDg8=","source":"AAAAAAFq7weqoCcQE7I=","target":"AAAAAAFqpyZaw1HqYaU="}
{"_parent":"AAAAAAFq7weqoCcQE7I=","visibility":"private","name":"sigCode","_type":"UMLAttribute","_id":"AAAAAAFq7weqoCcSu1Q=","type":"long"}
```

#### 其他

其他的一些操作在此不做过多描述，欢迎各位通过`-h`（或`--help`）参数查看帮助并探索。

## 注意事项

- **请确保构造函数正确实现，且类和构造函数均定义为`public`**，否则将无法进行实例化。
- **请保证传入的类继承了`UserApi`接口**，否则将无法载入。
- 此外，对于`ClassNotFoundException`（全称`com.oocourse.uml1.interact.exceptions.user.ClassNotFoundException`）等几个异常类，在 Java 的标准库里面有与之同名的类（全称`java.lang.ClassNotFoundException`）。**请各位在使用的时候注意甄别，以免误用**。
-

## 其他

- 如果还有不清楚的地方，**建议去阅读相关部分的源代码**（大部分地方均配有 javadoc 注释）。
