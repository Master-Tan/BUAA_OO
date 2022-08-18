package com.oocourse.uml2.models.common;

import com.oocourse.uml2.utils.string.WordUtils;

import java.util.List;
import java.util.function.Function;

/**
 * 消息类型
 */
public enum MessageSort implements CommonEnumStringifyExtension {
    SYNCH_CALL,
    ASYNCH_CALL,
    ASYNCH_SIGNAL,
    CREATE_MESSAGE,
    DELETE_MESSAGE,
    REPLY;

    private static final Function<String, String> ORIGINAL_TO_ENUM
            = ((Function<String, List<String>>) WordUtils::getWordsFromCamel)
            .andThen(WordUtils::getLargeUnderlineFromList);
    public static MessageSort DEFAULT = SYNCH_CALL;

    /**
     * 从原字符串加载
     *
     * @param originalString 原字符串
     * @return 消息类型
     */
    public static MessageSort loadFromString(String originalString) {
        return valueOf(ORIGINAL_TO_ENUM.apply(originalString));
    }
}
