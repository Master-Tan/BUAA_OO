package com.oocourse.uml2.interact.exceptions;

/**
 * AppRunner异常
 */
public abstract class AppRunnerProcessException extends AppRunnerException {
    private final Exception exception;

    /**
     * 构造函数
     *
     * @param exception 异常对象
     */
    AppRunnerProcessException(Exception exception) {
        super(exception.getMessage());
        this.exception = exception;
    }

    /**
     * 获取异常对象
     *
     * @return 异常对象
     */
    public Exception getException() {
        return exception;
    }
}
