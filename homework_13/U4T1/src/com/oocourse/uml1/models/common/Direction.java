package com.oocourse.uml1.models.common;

/**
 * 参数方向
 */
public enum Direction implements CommonEnumStringifyExtension {
    IN, // 对内（最常见的形式）
    INOUT, // 内外
    OUT,  // 对外
    RETURN;  // 返回（即一般的返回值）

    public static Direction DEFAULT = IN;

    /**
     * 从原字符串加载
     *
     * @param originalString 原字符串
     * @return 参数方向
     */
    public static Direction loadFromString(String originalString) {
        return valueOf(originalString.toUpperCase());
    }
}