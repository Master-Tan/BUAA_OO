package com.oocourse.uml1.utils.json;

/**
 * JSON包装类
 */
public class JsonObjectPackage implements OutputWithJson {
    private final Object jsonObject;

    /**
     * 构造函数
     *
     * @param jsonObject JSON对象
     */
    JsonObjectPackage(Object jsonObject) {
        this.jsonObject = jsonObject;
    }

    /**
     * 获取JSON对象
     *
     * @return JSON对象
     */
    @Override
    public Object toJson() {
        return this.jsonObject;
    }

    /**
     * 获取JSON对象
     *
     * @return JSON对象
     */
    public Object getJsonObject() {
        return jsonObject;
    }
}
