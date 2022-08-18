package com.oocourse.uml2.models.exceptions;

/**
 * JSON非列表异常
 */
public class UmlParseNotArrayException extends UmlParseException {
    /**
     * 构造函数
     *
     * @param jsonObject JSON对象
     */
    public UmlParseNotArrayException(Object jsonObject) {
        super("UML parse - Not an array.", jsonObject);
    }
}
