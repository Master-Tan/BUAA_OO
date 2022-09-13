package com.oocourse.uml1.models.common;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * 可见性
 */
public enum Visibility implements CommonEnumStringifyExtension {
    PUBLIC, // public
    PROTECTED,  // protected
    PRIVATE,  // private
    PACKAGE;  // package-private

    public static final Visibility DEFAULT = PUBLIC;
    private static final Map<Visibility, String> SHOWN_STRING =
            Collections.unmodifiableMap(new HashMap<Visibility, String>() {{
                put(PUBLIC, "public");
                put(PROTECTED, "protected");
                put(PRIVATE, "private");
                put(PACKAGE, "package-private");
            }});

    /**
     * 从原字符串加载
     *
     * @param originalString 原字符串
     * @return 可见性
     */
    public static Visibility loadFromString(String originalString) {
        return valueOf(originalString.toUpperCase());
    }

    /**
     * 获取一般形式
     *
     * @return 一般形式
     */
    public String getCommonString() {
        return SHOWN_STRING.get(this);
    }
}
