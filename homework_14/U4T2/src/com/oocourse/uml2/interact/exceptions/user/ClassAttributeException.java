package com.oocourse.uml2.interact.exceptions.user;

/**
 * 类属性异常
 */
public abstract class ClassAttributeException extends ClassException {
    private final String attributeName;

    /**
     * 构造函数
     *
     * @param message       异常信息
     * @param className     类名
     * @param attributeName 属性名
     */
    public ClassAttributeException(String message, String className, String attributeName) {
        super(message, className);
        this.attributeName = attributeName;
    }

    /**
     * 获取属性名
     *
     * @return 属性名
     */
    public String getAttributeName() {
        return attributeName;
    }
}
