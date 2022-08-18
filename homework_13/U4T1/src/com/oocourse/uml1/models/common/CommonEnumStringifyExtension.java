package com.oocourse.uml1.models.common;

/**
 * 枚举转字符串
 */
public interface CommonEnumStringifyExtension {
    /**
     * 获取字符串形式
     *
     * @return 字符串形式
     */
    String toString();

    /**
     * 获取小写字符串形式
     *
     * @return 小写字符串形式
     */
    default String toLowerCaseString() {
        return toString().toLowerCase();
    }

    /**
     * 获取大写字符串形式
     *
     * @return 大写字符串形式
     */
    default String toUpperCaseString() {
        return toString().toUpperCase();
    }

    /**
     * 获取单词首字母大写形式
     *
     * @return 单词首字母大写形式
     */
    default String getCapitalizedString() {
        String[] words = toString().split("_");
        StringBuilder builder = new StringBuilder();
        for (String word : words) {
            builder.append(word.substring(0, 1).toUpperCase());
            builder.append(word.substring(1).toLowerCase());
        }
        return builder.toString();
    }
}
