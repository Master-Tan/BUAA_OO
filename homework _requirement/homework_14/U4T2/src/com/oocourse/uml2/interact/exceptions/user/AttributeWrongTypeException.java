package com.oocourse.uml2.interact.exceptions.user;

/**
 * 属性类型错误异常
 */
public class AttributeWrongTypeException extends ClassAttributeException {
    /**
     * 构造函数
     *
     * @param className     类名
     * @param attributeName 属性名
     */
    public AttributeWrongTypeException(String className, String attributeName) {
        super(String.format("Failed, wrong type of attribute \"%s\" in class \"%s\".",
                attributeName, className), className, attributeName);
    }
}
