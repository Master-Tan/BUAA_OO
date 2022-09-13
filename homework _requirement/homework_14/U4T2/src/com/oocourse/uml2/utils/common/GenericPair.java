package com.oocourse.uml2.utils.common;

import java.util.Objects;

/**
 * 通用二元对模型
 *
 * @param <X> 第一类
 * @param <Y> 第二类
 */
public class GenericPair<X, Y> {
    private final X firstValue;
    private final Y secondValue;

    /**
     * 构造函数
     *
     * @param firstValue  第一值
     * @param secondValue 第二值
     */
    public GenericPair(X firstValue, Y secondValue) {
        this.firstValue = firstValue;
        this.secondValue = secondValue;
    }

    /**
     * 获取第一个值
     *
     * @return 第一个值
     */
    public X getFirstValue() {
        return firstValue;
    }

    /**
     * 获取第二个值
     *
     * @return 第二个值
     */
    public Y getSecondValue() {
        return secondValue;
    }

    /**
     * 相等性判定
     *
     * @param o 对象
     * @return 相等性
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        GenericPair<?, ?> that = (GenericPair<?, ?>) o;
        return Objects.equals(firstValue, that.firstValue) &&
                Objects.equals(secondValue, that.secondValue);
    }

    /**
     * 哈希值求解
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(firstValue, secondValue);
    }

    /**
     * 转为字符串形式
     *
     * @return 字符串形式
     */
    @Override
    public String toString() {
        return "GenericPair{" +
                "firstValue=" + firstValue +
                ", secondValue=" + secondValue +
                '}';
    }
}
