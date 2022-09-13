package com.oocourse.uml1.interact.exceptions.user;

/**
 * 方法参数类型错误异常
 */
public class MethodWrongTypeException extends ClassMethodException {
    /**
     * 构造函数
     *
     * @param className  类名
     * @param methodName 方法名
     */
    public MethodWrongTypeException(String className, String methodName) {
        super(String.format(
                "Failed, wrong type of parameters or return value in method \"%s\" of class \"%s\".",
                methodName, className), className, methodName);
    }
}
