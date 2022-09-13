package com.oocourse.uml1.interact.exceptions.user;

/**
 * 构造函数
 */
public class ClassNotFoundException extends ClassException {
    /**
     * 构造函数
     *
     * @param className 类名
     */
    public ClassNotFoundException(String className) {
        super(String.format("Failed, class \"%s\" not found", className), className);
    }
}
