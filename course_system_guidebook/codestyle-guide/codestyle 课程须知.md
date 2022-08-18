# codestyle-guide
java 代码风格指导文档及相关工具

## 分数计算方式

- 每次作业代码风格部分默认总分为100分，采用扣分制
- 对于设计风格类（即风格文档的第六节）部分
  - 类长度风格问题，**每个扣50分**
  - 可见性检查、方法长度问题，**每个扣20分**
  - 参数个数、循环嵌套、语句嵌套问题，**每个扣10分**
  - 嵌套内联条件、布尔表达式、参数赋值问题，**每个扣5分**
- 对于命名约定类（即风格文档第五章）部分
  - 所有的问题，**每个扣5分**
- 对于除此之外的问题，**每个扣2分**
- **对于所有的问题扣分上不封顶，扣到0分为止**

## 常见问题

### Q：作业中会如何检查代码风格？

A：我们会使用一个叫做 `checkstyle` 的 Java 代码风格检查工具进行代码风格的检查。其中配置文件使用本仓库内提供的 `config.xml` 文件 （见 http://gitlab.oo.buaa.edu.cn/2022_public/checkstyle_config），作为代码风格检查的依据。

值得注意的是，我们的检查对象为你的代码仓库内全部的 `.java` 文件，其他的文件会被系统自动忽略。

### Q：我们本地是否可以检查代码风格？

A：当然可以。你们有以下几种方法检测自己的代码风格：

* 从Checkstyle 官网上下载 checkstyle 的 jar 文件，并在本机按照help里提供的命令行参数进行代码风格的检查。
* 对于ubuntu（应该其他 unix 系统也行，但是只在 ubuntu 上试过）用户，可以使用我们封装的 `pycheckstyle` Python 包进行快速代码风格检测（目前仅支持Python3）

* 【推荐】**对于 IDEA 用户，可以下载安装`Checkstyle-IDEA`插件（见下文），对 ide 内的代码进行实时风格检测。只需要安装好插件后在设置中将我们提供的 `config.xml` 载入即可。**（更详细的攻略可以自行百度）
* 对于 Eclipse 用户，实际上也存在 checkstyle 支持，可以自行百度探索。

### Q：代码风格文档内是否会和配置文件等存在冲突？如果存在，如何处理？

A：我们的文档主要是将官方文档中相关的部分进行一些较为通俗的解释，可能有些细节上确实不够，也有可能存在少量的偏差。对于这样的情况，我们以 checkstyle 的官方文档，以及 `checkstyle` 在使用 `config.xml` 时的实际检查结果为准。

### Q：我们如何去查看官方文档的对应规则？

A：在我们提供的风格文档中，均将配置文件中的对应部分写了出来。可以根据 `module` 的 `name` 字段信息，在官方文档上查找对应的规则以及说明。

## 一些有用的资料

* [Checkstyle官方文档（全英文版）](http://checkstyle.sourceforge.net/checks.html)
* [Google官方代码规范（我们所使用的代码规范的原型）](https://google.github.io/styleguide/javaguide.html)
* [Sun官方代码规范](http://java.sun.com/docs/books/jls/second_edition/html/index.html)
* [【推荐】IDEA Checkstyle插件主页](http://plugins.jetbrains.com/plugin/1065-checkstyle-idea)
* [【课程组提供】pycheckstyle封装包](https://github.com/OO-guide-2019/pycheckstyle)


## 关于作者
 * [PaParaZz1]
 * [HansBug](mailto:hansbug@questionor.cn)，邮箱：hansbug@questionor.cn

如有问题或建议，欢迎联系作者。
