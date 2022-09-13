package com.oocourse.uml2.models.common;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

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
    UML_INTERFACE,
    UML_STATE_MACHINE,
    UML_REGION,
    UML_STATE,
    UML_PSEUDOSTATE,
    UML_FINAL_STATE,
    UML_TRANSITION,
    UML_EVENT,
    UML_OPAQUE_BEHAVIOR,
    UML_COLLABORATION,
    UML_INTERACTION,
    UML_LIFELINE,
    UML_MESSAGE,
    UML_ENDPOINT;

    /**
     * 类模型子集
     */
    public static final Set<ElementType> MODEL_SUBSET
            = Collections.unmodifiableSet(new HashSet<ElementType>() {{
        add(UML_CLASS);
        add(UML_ASSOCIATION);
        add(UML_ASSOCIATION_END);
        add(UML_ATTRIBUTE);
        add(UML_OPERATION);
        add(UML_PARAMETER);
        add(UML_GENERALIZATION);
        add(UML_INTERFACE_REALIZATION);
        add(UML_INTERFACE);
    }});

    /**
     * 状态图子集
     */
    public static final Set<ElementType> STATE_MACHINE_SUBSET
            = Collections.unmodifiableSet(new HashSet<ElementType>() {{
        add(UML_STATE_MACHINE);
        add(UML_REGION);
        add(UML_STATE);
        add(UML_PSEUDOSTATE);
        add(UML_FINAL_STATE);
        add(UML_TRANSITION);
        add(UML_EVENT);
        add(UML_OPAQUE_BEHAVIOR);
    }});

    /**
     *
     */
    public static final Set<ElementType> COLLABORATION_SUBSET
            = Collections.unmodifiableSet(new HashSet<ElementType>() {{
        add(UML_COLLABORATION);
        add(UML_ATTRIBUTE);
        add(UML_INTERACTION);
        add(UML_LIFELINE);
        add(UML_MESSAGE);
        add(UML_ENDPOINT);
    }});

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
