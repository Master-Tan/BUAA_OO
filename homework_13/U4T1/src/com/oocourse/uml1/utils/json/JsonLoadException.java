package com.oocourse.uml1.utils.json;

/**
 * JSON加载异常
 */
public class JsonLoadException extends Exception {
    private final Object jsonObject;

    /**
     * 构造函数
     *
     * @param message    异常信息
     * @param jsonObject JSON数据对象
     */
    public JsonLoadException(String message, Object jsonObject) {
        super(message);
        this.jsonObject = jsonObject;
    }

    /**
     * 获取JSON数据对象
     */
    public Object getJsonObject() {
        return jsonObject;
    }
}
