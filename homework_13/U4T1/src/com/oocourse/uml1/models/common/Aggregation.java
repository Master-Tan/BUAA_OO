package com.oocourse.uml1.models.common;

/**
 * 聚合关系
 */
public enum Aggregation implements CommonEnumStringifyExtension {
    NONE,  // 无聚合
    SHARED,  // 共享关系
    COMPOSITE;  // 复合关系

    public static final Aggregation DEFAULT = NONE;

    /**
     * 从字符串加载
     *
     * @param originalString 原字符串
     * @return 聚合关系
     */
    public static Aggregation loadFromString(String originalString) {
        return valueOf(originalString.toUpperCase());
    }
}

