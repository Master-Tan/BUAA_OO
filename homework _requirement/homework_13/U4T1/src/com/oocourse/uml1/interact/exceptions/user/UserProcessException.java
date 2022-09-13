package com.oocourse.uml1.interact.exceptions.user;

/**
 * AppRunner失败结果异常
 * 用于传出Failed消息
 */
public abstract class UserProcessException extends Exception {
    /**
     * 构造函数
     *
     * @param message 异常消息
     */
    public UserProcessException(String message) {
        super(message);
    }
}
