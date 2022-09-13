package com.oocourse.uml1.interact.exceptions;

/**
 * 基本异常类
 */
public abstract class ApplicationException extends Exception {
    /**
     * 构造函数
     *
     * @param message 异常消息
     */
    ApplicationException(String message) {
        super(message);
    }
}
