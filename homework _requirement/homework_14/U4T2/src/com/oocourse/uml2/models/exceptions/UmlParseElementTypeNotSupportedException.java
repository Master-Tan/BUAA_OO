package com.oocourse.uml2.models.exceptions;

import com.oocourse.uml2.models.common.ElementType;

/**
 * 元素类型暂不支持解析异常
 */
public class UmlParseElementTypeNotSupportedException extends UmlParseException {
    private final ElementType elementType;

    /**
     * 构造函数
     *
     * @param jsonObject  解析数据
     * @param elementType 元素类型
     */
    public UmlParseElementTypeNotSupportedException(Object jsonObject, ElementType elementType) {
        super(String.format("UML parse - Element type \"%s\" not supported.",
                elementType.getOriginalString()), jsonObject);
        this.elementType = elementType;
    }

    /**
     * 获取元素类型
     *
     * @return 元素类型
     */
    public ElementType getElementType() {
        return elementType;
    }
}
