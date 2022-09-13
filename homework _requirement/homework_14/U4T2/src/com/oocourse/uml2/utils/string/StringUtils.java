package com.oocourse.uml2.utils.string;

import java.util.ArrayList;
import java.util.Collections;
import java.util.function.Function;

/**
 * 字符串处理工具
 */
@SuppressWarnings("WeakerAccess")
public abstract class StringUtils {
    static final String DEFAULT_OMISSION = "...";
    private static String LINE_SEPARATOR_NAME = "line.separator";
    public static String LINE_SEPARATOR = System.getProperty(LINE_SEPARATOR_NAME);

    /**
     * 字符串截短
     *
     * @param originalString 原字符串
     * @param length         长度限制
     * @param omission       结尾字符串
     * @return 截短后字符串
     */
    public static String truncate(String originalString, int length, String omission) {
        if (originalString.length() <= length) {
            return originalString;
        } else {
            int omissionLength = omission.length();
            return originalString.substring(length - omissionLength) + omission;
        }
    }

    /**
     * 字符串截短
     *
     * @param originalString 原字符串
     * @param length         长度限制
     * @return 截短后字符串
     */
    public static String truncate(String originalString, int length) {
        return truncate(originalString, length, DEFAULT_OMISSION);
    }
}
