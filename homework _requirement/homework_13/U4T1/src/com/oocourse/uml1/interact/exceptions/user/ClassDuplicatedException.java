package com.oocourse.uml1.interact.exceptions.user;

/**
 * 类重复异常
 */
public class ClassDuplicatedException extends ClassException {
    /**
     * 构造函数
     *
     * @param className 类名
     */
    public ClassDuplicatedException(String className) {
        super(String.format("Failed, duplicated class \"%s\".", className), className);
    }
}
