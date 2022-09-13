package com.oocourse.uml2.interact.parser;

import com.oocourse.uml2.interact.exceptions.ArgumentNotEnoughException;
import com.oocourse.uml2.interact.exceptions.ArgumentTooManyException;
import com.oocourse.uml2.interact.exceptions.ClassUnableToParseException;
import com.oocourse.uml2.interact.exceptions.InputArgumentException;
import com.oocourse.uml2.interact.exceptions.ParseArgumentException;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * 参数列表解析器
 * 说明：
 * 1、此类的基本原理是，通过调用此类型的valueOf方法，来进行数据自动解析
 * 2、这算是半个黑科技，用来对付输入处理效果拔群且可维护性极好
 * 3、感兴趣的的话可以读一读，并玩一玩（此类均设置为public）
 */
@SuppressWarnings({"WeakerAccess", "RedundantStringConstructorCall"})
public class InputArgumentParser {
    private static final String VALUE_OF_METHOD_NAME = "valueOf";
    private final List<Class<?>> classes;
    private final Class<?> remainsArgumentClass;

    /**
     * 构造函数
     *
     * @param classes              参数类型列表
     * @param remainsArgumentClass 变长参数类型（null表示无变长参数）
     */
    private InputArgumentParser(Class<?>[] classes, Class<?> remainsArgumentClass) {
        this.classes = Arrays.asList(classes);
        this.remainsArgumentClass = remainsArgumentClass;
    }

    /**
     * 构造函数
     *
     * @param classes 参数类型列表
     */
    private InputArgumentParser(Class<?>... classes) {
        this(classes, null);
    }

    /**
     * 创建实例
     *
     * @param classes 参数类型列表
     * @return 解析器实例
     */
    public static InputArgumentParser newInstance(Class<?>... classes) {
        return new InputArgumentParser(classes);
    }

    /**
     * 创建实例
     *
     * @param classes              参数类型列表
     * @param remainsArgumentClass 变长参数类型
     * @return 解析器实例
     */
    public static InputArgumentParser newInstance(Class<?>[] classes, Class<?> remainsArgumentClass) {
        return new InputArgumentParser(classes, remainsArgumentClass);
    }

    /**
     * 获取参数类型列表
     *
     * @return 参数类型列表
     */
    public List<Class<?>> getClasses() {
        return classes;
    }

    /**
     * 获取变长参数类型
     *
     * @return 变长参数类型
     */
    public Class<?> getRemainsArgumentClass() {
        return remainsArgumentClass;
    }

    /**
     * 参数列表解析
     *
     * @param arguments 参数列表
     * @return 解析对象列表
     * @throws InputArgumentException 输入参数处理异常
     */
    public List<Object> parse(String[] arguments) throws InputArgumentException {
        ArrayList<Object> list = new ArrayList<>();
        if (arguments.length < this.classes.size()) {
            throw new ArgumentNotEnoughException(this.classes.size(), arguments.length);
        }
        if (arguments.length > this.classes.size() && this.remainsArgumentClass == null) {
            throw new ArgumentTooManyException(this.classes.size(), arguments.length);
        }

        int baseLength = this.classes.size();
        for (int i = 0; i < arguments.length; i++) {
            Class<?> cls;
            if (i < baseLength) {
                cls = this.classes.get(i);
            } else {
                cls = this.remainsArgumentClass;
            }

            Object value;
            String argument = arguments[i];
            if (cls == String.class) {
                value = new String(argument);
            } else {
                Method valueOfMethod;
                try {
                    valueOfMethod = cls.getMethod(VALUE_OF_METHOD_NAME, String.class);
                    if (!(Modifier.isStatic(valueOfMethod.getModifiers()) &&
                            Modifier.isPublic(valueOfMethod.getModifiers()))) {
                        throw new NoSuchMethodException(VALUE_OF_METHOD_NAME);
                    }
                } catch (NoSuchMethodException e) {
                    throw new ClassUnableToParseException(cls);
                }

                try {
                    value = valueOfMethod.invoke(null, argument);
                } catch (Exception e) {
                    throw new ParseArgumentException(cls, argument);
                }
            }
            list.add(value);
        }
        return list;
    }

    /**
     * 行数据解析
     *
     * @param line           参数列表
     * @param splitterRegexp 分隔符正则表达式
     * @return 解析对象列表
     * @throws InputArgumentException 输入参数处理异常
     */
    public List<Object> parse(String line, String splitterRegexp) throws InputArgumentException {
        String[] arguments = line.split(splitterRegexp);
        return parse(arguments);
    }
}
