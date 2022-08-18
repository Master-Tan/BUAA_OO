package com.oocourse.uml2.interact.exceptions;

/**
 * AppRunner运行异常
 */
public class AppRunnerRunException extends AppRunnerProcessException {
    /**
     * 构造函数
     *
     * @param exception 运行异常对象
     */
    public AppRunnerRunException(Exception exception) {
        super(exception);
    }
}
