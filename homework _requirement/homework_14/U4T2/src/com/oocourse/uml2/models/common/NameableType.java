package com.oocourse.uml2.models.common;

import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.utils.json.OutputWithJson;

import java.util.Map;

/**
 * 加载类别信息
 * 主要用于可以指定类别依赖，也可以指定字符串类名的情况
 */
public interface NameableType extends OutputWithJson {
    /**
     * 从json加载数据
     *
     * @param jsonObject json数据
     * @return 类别信息
     */
    static NameableType loadFromJson(Object jsonObject) {
        if (jsonObject instanceof Map) {
            Map mapObject = (Map) jsonObject;
            String referenceId = (String) mapObject.get(UmlElement.REF_KEY);
            return new ReferenceType(referenceId);
        } else {
            String name = (String) jsonObject;
            return new NamedType(name);
        }
    }
}
