package com.oocourse.uml2.models.common;

import com.oocourse.uml2.utils.string.WordUtils;

import java.util.List;
import java.util.function.Function;

/**
 * 枚举转字符串
 */
public interface CommonEnumStringifyExtension {
    Function<String, String> ENUM_TO_LARGE_CAMEL
            = ((Function<String, List<String>>) WordUtils::getWordsFromUnderline)
            .andThen(WordUtils::getLargeCamelFromList);
    Function<String, String> ENUM_TO_SMALL_CAMEL
            = ((Function<String, List<String>>) WordUtils::getWordsFromUnderline)
            .andThen(WordUtils::getSmallCamelFromList);

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
     * 获取大驼峰形式
     *
     * @return 大驼峰形式
     */
    default String toLargeCamelString() {
        return ENUM_TO_LARGE_CAMEL.compose(Object::toString).apply(this);
    }

    /**
     * 获取小驼峰形式
     *
     * @return 小驼峰形式
     */
    default String toSmallCamelString() {
        return ENUM_TO_SMALL_CAMEL.compose(Object::toString).apply(this);
    }

    /**
     * 获取字符串原形式
     *
     * @return 原形式
     */
    default String getOriginalString() {
        return toSmallCamelString();
    }
}
