package com.oocourse.uml2.models.exceptions;

import com.oocourse.uml2.utils.json.JsonLoadException;

/**
 * UML解析异常
 */
public abstract class UmlParseException extends JsonLoadException {

    /**
     * 构造函数
     *
     * @param message    异常信息
     * @param jsonObject 解析数据
     */
    public UmlParseException(String message, Object jsonObject) {
        super(message, jsonObject);
    }
}
