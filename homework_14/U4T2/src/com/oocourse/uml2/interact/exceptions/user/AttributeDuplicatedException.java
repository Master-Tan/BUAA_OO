package com.oocourse.uml2.interact.exceptions.user;

/**
 * 属性重复异常
 */
public class AttributeDuplicatedException extends ClassAttributeException {
    /**
     * 构造函数
     *
     * @param className     类名
     * @param attributeName 属性名
     */
    public AttributeDuplicatedException(String className, String attributeName) {
        super(String.format("Failed, duplicated attribute \"%s\" in class \"%s\".",
                attributeName, className), className, attributeName);
    }
}
