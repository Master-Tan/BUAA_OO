package com.oocourse.uml2.utils.common;

import java.util.Objects;

/**
 * 对象容器
 *
 * @param <T> 包含类型
 */
public class GenericContainer<T> {
    private final T content;

    /**
     * 构造函数
     *
     * @param content 内容
     */
    protected GenericContainer(T content) {
        this.content = content;
    }

    /**
     * 获取包含对象
     *
     * @return 包含对象
     */
    protected T getContent() {
        return content;
    }

    /**
     * 判断相等性
     *
     * @param o 对象
     * @return 是否相等
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        GenericContainer<?> that = (GenericContainer<?>) o;
        return Objects.equals(content, that.content);
    }

    /**
     * 求哈希值
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(content);
    }

    /**
     * 获取字符串形式
     *
     * @return 字符串
     */
    @Override
    public String toString() {
        return "GenericContainer{" +
                "content=" + content +
                '}';
    }
}
