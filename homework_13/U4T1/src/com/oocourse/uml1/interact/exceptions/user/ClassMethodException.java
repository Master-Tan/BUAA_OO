package com.oocourse.uml1.interact.exceptions.user;

/**
 * 类方法异常
 */
public abstract class ClassMethodException extends ClassException {
    private final String methodName;

    /**
     * 构造函数
     *
     * @param message    异常信息
     * @param className  类名
     * @param methodName 方法名
     */
    public ClassMethodException(String message, String className, String methodName) {
        super(message, className);
        this.methodName = methodName;
    }

    /**
     * 获取方法名
     *
     * @return 方法名
     */
    public String getMethodName() {
        return methodName;
    }
}
