package com.oocourse.uml2.models.exceptions;

/**
 * UML解析key未找到异常
 */
public class UmlParseKeyNotFoundException extends UmlParseException {
    private final String key;

    /**
     * 构造函数
     *
     * @param jsonObject JSON对象
     * @param key        key
     */
    public UmlParseKeyNotFoundException(Object jsonObject, String key) {
        super(String.format("UML parse - Key \"%s\" not found.", key), jsonObject);
        this.key = key;
    }

    /**
     * 获取key
     *
     * @return key
     */
    public String getKey() {
        return key;
    }
}
