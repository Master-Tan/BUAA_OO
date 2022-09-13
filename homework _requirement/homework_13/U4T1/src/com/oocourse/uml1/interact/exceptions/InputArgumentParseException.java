package com.oocourse.uml1.interact.exceptions;

/**
 * 输入参数解析异常
 */
public abstract class InputArgumentParseException
        extends InputArgumentException {
    private final Class<?> errorClass;
    private final String errorString;

    /**
     * 构造函数
     *
     * @param message     异常消息
     * @param errorClass  异常类型
     * @param errorString 异常字符串参数
     */
    InputArgumentParseException(
            String message, Class<?> errorClass, String errorString) {
        super(message);
        this.errorClass = errorClass;
        this.errorString = errorString;
    }

    /**
     * 获取异常类型
     *
     * @return 异常类型
     */
    public Class<?> getErrorClass() {
        return errorClass;
    }

    /**
     * 获取异常字符串参数
     *
     * @return 异常字符串参数
     */
    public String getErrorString() {
        return errorString;
    }
}
