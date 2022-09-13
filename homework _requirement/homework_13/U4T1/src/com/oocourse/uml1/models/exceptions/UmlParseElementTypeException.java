package com.oocourse.uml1.models.exceptions;

import com.oocourse.uml1.models.common.ElementType;

/**
 * 非法元素类型异常
 */
public class UmlParseElementTypeException extends UmlParseException {
    private final ElementType elementType;

    /**
     * 构造函数
     *
     * @param jsonObject  解析数据
     * @param elementType 元素类型
     */
    public UmlParseElementTypeException(Object jsonObject, ElementType elementType) {
        super(String.format("UML parse - Invalid element type %s.", elementType), jsonObject);
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
