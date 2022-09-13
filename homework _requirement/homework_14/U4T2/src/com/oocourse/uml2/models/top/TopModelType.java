package com.oocourse.uml2.models.top;

import com.oocourse.uml2.models.common.ElementTypeStringifyExtension;

import java.util.HashMap;

/**
 * 顶层模型类别
 */
public enum TopModelType implements ElementTypeStringifyExtension {
    UML_MODEL,
    UML_STATE_MACHINE,
    UML_COLLABORATION;

    /**
     * 原字符串转元素类型映射
     */
    private static final HashMap<String, TopModelType> ORIGINAL_STRING_TO_ELEMENT_TYPE
            = new HashMap<String, TopModelType>() {{
        for (TopModelType topModelType : TopModelType.values()) {
            put(topModelType.getOriginalString(), topModelType);
        }
    }};

    /**
     * 原字符串转元素类型
     *
     * @param originalString 原字符串
     * @return 元素类型
     */
    public static TopModelType loadFromOriginalString(String originalString) {
        return ORIGINAL_STRING_TO_ELEMENT_TYPE.get(originalString);
    }

    /**
     * 判断原字符串是否存在
     *
     * @param originalString 原字符串
     * @return 是否存在
     */
    public static boolean containsOriginalString(String originalString) {
        return ORIGINAL_STRING_TO_ELEMENT_TYPE.containsKey(originalString);
    }
}
