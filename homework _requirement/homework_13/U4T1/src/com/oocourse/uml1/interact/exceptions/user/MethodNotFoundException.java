package com.oocourse.uml1.interact.exceptions.user;

/**
 * 方法未找到异常
 */
public class MethodNotFoundException extends ClassMethodException {
    /**
     * 构造函数
     *
     * @param className  类名
     * @param methodName 方法名
     */
    public MethodNotFoundException(String className, String methodName) {
        super(String.format("Failed, method \"%s\" not found in class \"%s\".",
                methodName, className), className, methodName);
    }
}
