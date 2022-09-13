package com.oocourse.uml2.models.exceptions;

/**
 * JSON非对象异常
 */
public class UmlParseNotObjectException extends UmlParseException {
    /**
     * 构造函数
     *
     * @param jsonObject JSON对象
     */
    public UmlParseNotObjectException(Object jsonObject) {
        super("UML parse - Not an object.", jsonObject);
    }
}
