package com.oocourse.uml2.utils.string;

import java.util.Objects;
import java.util.function.Function;

/**
 * 动态字符串
 *
 * @param <T> 原类型
 */
public class DynamicString<T> {
    private static final Function<Object, String> DEFAULT_TRANSFORMER = String::valueOf;
    private final T object;
    private final Function<? super T, String> transformer;

    /**
     * 构造函数
     *
     * @param object      原对象
     * @param transformer 字符串转换函数
     */
    public DynamicString(T object, Function<? super T, String> transformer) {
        this.object = object;
        this.transformer = transformer;
    }

    /**
     * 构造函数
     *
     * @param object 原对象
     */
    public DynamicString(T object) {
        this.object = object;
        this.transformer = DEFAULT_TRANSFORMER;
    }

    /**
     * 获取原对象
     *
     * @return 原对象
     */
    public T getObject() {
        return object;
    }

    /**
     * 获取转换函数
     *
     * @return 转换函数
     */
    public Function<? super T, String> getTransformer() {
        return transformer;
    }

    /**
     * 获取字符串形式
     *
     * @return 字符串形式
     */
    @Override
    public String toString() {
        return transformer.apply(object);
    }

    /**
     * 判断相等性
     *
     * @param o 对象
     * @return 相等性
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        DynamicString<?> that = (DynamicString<?>) o;
        return Objects.equals(object, that.object) &&
                Objects.equals(transformer, that.transformer);
    }

    /**
     * 获取哈希值
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(object, transformer);
    }
}
