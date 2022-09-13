package com.oocourse.uml1.interact.exceptions;

/**
 * AppRunner对象实例化异常
 */
public class AppRunnerInstantiationException extends AppRunnerProcessException {
    /**
     * 构造函数
     *
     * @param exception 异常类
     */
    public AppRunnerInstantiationException(Exception exception) {
        super(exception);
    }
}
