package com.oocourse.uml2.interact.common;

import java.util.Objects;

/**
 * 属性类信息
 */
public class AttributeClassInformation implements Comparable<AttributeClassInformation> {
    private final String attributeName;
    private final String className;

    /**
     * 构造函数
     *
     * @param attributeName 属性名称
     * @param className     类名称
     */
    public AttributeClassInformation(String attributeName, String className) {
        this.attributeName = attributeName;
        this.className = className;
    }

    /**
     * 获取属性名称
     *
     * @return 属性名称
     */
    public String getAttributeName() {
        return attributeName;
    }

    /**
     * 获取类名称
     *
     * @return 类名称
     */
    public String getClassName() {
        return className;
    }

    /**
     * 相等性判定
     *
     * @param o 对象
     * @return 是否相等
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        AttributeClassInformation that = (AttributeClassInformation) o;
        return Objects.equals(attributeName, that.attributeName) &&
                Objects.equals(className, that.className);
    }

    /**
     * 哈希值求解
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(attributeName, className);
    }

    /**
     * 大小比较
     *
     * @param that 另一个类
     * @return 比较结果
     */
    @Override
    public int compareTo(AttributeClassInformation that) {
        int compareFirst = this.getClassName().compareTo(that.getClassName());
        if (compareFirst != 0) {
            return compareFirst;
        } else {
            return this.getAttributeName().compareTo(that.getAttributeName());
        }
    }
}
