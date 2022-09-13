package com.oocourse.uml2.models.common;

import java.util.Objects;

/**
 * 命名型类别信息
 * （字符串命名）
 */
public class NamedType implements NameableType {
    private final String name;

    /**
     * 构造函数
     *
     * @param name 名称
     */
    NamedType(String name) {
        this.name = name;
    }

    /**
     * 获取名称
     *
     * @return 名称
     */
    public String getName() {
        return name;
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
        NamedType namedType = (NamedType) o;
        return Objects.equals(name, namedType.name);
    }

    /**
     * 哈希值求解
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    /**
     * 转为json数据
     *
     * @return json数据
     */
    public Object toJson() {
        return this.name;
    }
}
