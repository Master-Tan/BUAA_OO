package com.oocourse.uml1.interact.exceptions.user;

/**
 * 类异常
 */
public abstract class ClassException extends UserProcessException {
    private final String className;

    /**
     * 构造函数
     *
     * @param message   异常信息
     * @param className 类名
     */
    public ClassException(String message, String className) {
        super(message);
        this.className = className;
    }

    /**
     * 获取类名
     *
     * @return 类名
     */
    public String getClassName() {
        return className;
    }
}
