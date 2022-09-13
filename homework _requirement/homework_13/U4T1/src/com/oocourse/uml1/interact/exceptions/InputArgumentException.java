package com.oocourse.uml1.interact.exceptions;

/**
 * 输入参数异常
 */
public abstract class InputArgumentException extends ApplicationException {
    /**
     * 构造函数
     *
     * @param message 异常信息
     */
    InputArgumentException(String message) {
        super(message);
    }
}
