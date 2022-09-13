package com.oocourse.uml2.interact.exceptions.user;

/**
 * 属性未找到异常
 */
public class AttributeNotFoundException extends ClassAttributeException {
    /**
     * 构造函数
     *
     * @param className     类名
     * @param attributeName 属性名
     */
    public AttributeNotFoundException(String className, String attributeName) {
        super(String.format("Failed, attribute \"%s\" not found in class \"%s\".",
                attributeName, className), className, attributeName);
    }
}
