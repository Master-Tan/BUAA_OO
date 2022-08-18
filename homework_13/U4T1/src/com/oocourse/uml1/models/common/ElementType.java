package com.oocourse.uml1.models.common;

import java.util.HashMap;
import java.util.HashSet;

/**
 * 元素类型
 */
public enum ElementType implements ElementTypeStringifyExtension {
    UML_CLASS,
    UML_ASSOCIATION,
    UML_ASSOCIATION_END,
    UML_ATTRIBUTE,
    UML_OPERATION,
    UML_PARAMETER,
    UML_GENERALIZATION,
    UML_INTERFACE_REALIZATION,
    UML_INTERFACE;

    /**
     * 类模型子集
     */
    public static final HashSet<ElementType> MODEL_SUBSET
            = new HashSet<ElementType>() {{
        add(UML_CLASS);
        add(UML_ASSOCIATION);
        add(UML_ASSOCIATION_END);
        add(UML_ATTRIBUTE);
        add(UML_OPERATION);
        add(UML_PARAMETER);
        add(UML_GENERALIZATION);
        add(UML_INTERFACE_REALIZATION);
        add(UML_INTERFACE);
    }};

    /**
     * 原字符串转元素类型映射
     */
    private static final HashMap<String, ElementType> ORIGINAL_STRING_TO_ELEMENT_TYPE
            = new HashMap<String, ElementType>() {{
        for (ElementType elementType : ElementType.values()) {
            put(elementType.getOriginalString(), elementType);
        }
    }};

    /**
     * 原字符串转元素类型
     *
     * @param originalString 原字符串
     * @return 元素类型
     */
    public static ElementType loadFromOriginalString(String originalString) {
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
