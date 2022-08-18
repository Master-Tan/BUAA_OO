package com.oocourse.uml1.models.common;

/**
 * 元素类型字符化扩展
 */
public interface ElementTypeStringifyExtension {
    /**
     * 获取原枚举字符串值
     *
     * @return 原枚举字符串值
     */
    String toString();

    /**
     * 获取原生字符串值
     *
     * @return 原生字符串值
     */
    default String getOriginalString() {
        String[] words = toString().split("_");
        StringBuilder builder = new StringBuilder();
        builder.append(words[0].toUpperCase());
        for (int i = 1; i < words.length; i++) {
            String word = words[i];
            builder.append(word.substring(0, 1).toUpperCase());
            builder.append(word.substring(1).toLowerCase());
        }
        return builder.toString();
    }
}
