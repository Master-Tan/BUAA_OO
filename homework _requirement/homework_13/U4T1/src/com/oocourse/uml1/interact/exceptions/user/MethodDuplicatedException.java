package com.oocourse.uml1.interact.exceptions.user;

/**
 * 方法重复异常
 */
public class MethodDuplicatedException extends ClassMethodException {
    /**
     * 构造函数
     *
     * @param className  类名
     * @param methodName 方法名
     */
    public MethodDuplicatedException(String className, String methodName) {
        super(String.format("Failed, duplicated method \"%s\" in class \"%s\".",
                methodName, className), className, methodName);
    }
}
