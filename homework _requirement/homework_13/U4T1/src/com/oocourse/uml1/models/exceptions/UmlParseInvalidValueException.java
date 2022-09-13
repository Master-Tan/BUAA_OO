package com.oocourse.uml1.models.exceptions;

/**
 * 非法数值异常
 */
public class UmlParseInvalidValueException extends UmlParseException {
    private final Object value;

    /**
     * 构造函数
     *
     * @param jsonObject JSON对象
     * @param value      数值
     */
    public UmlParseInvalidValueException(Object jsonObject, Object value) {
        super(String.format("UML parse - Invalid value %s.", value), jsonObject);
        this.value = value;
    }

    /**
     * 获取数值
     *
     * @return 数值
     */
    public Object getValue() {
        return value;
    }
}
