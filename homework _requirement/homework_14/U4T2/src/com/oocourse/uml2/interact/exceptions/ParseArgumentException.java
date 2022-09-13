package com.oocourse.uml2.interact.exceptions;

/**
 * 参数解析失败
 */
public class ParseArgumentException extends InputArgumentParseException {
    /**
     * 构造函数
     *
     * @param errorClass  异常类型
     * @param errorString 异常字符串参数
     */
    public ParseArgumentException(Class<?> errorClass, String errorString) {
        super("Argument parse failed.", errorClass, errorString);
    }
}
