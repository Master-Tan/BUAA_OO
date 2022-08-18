package com.oocourse.uml2.models.top;

import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.utils.common.GenericPair;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * 顶层模型池
 */
public class StarumlFileTopModels {
    private static final String OWNED_ELEMENTS_KEY = "ownedElements";
    private final Object jsonObject;
    private final HashMap<ModelKey, Object> models;

    /**
     * 构造函数
     *
     * @param jsonObject json数据
     */
    private StarumlFileTopModels(Object jsonObject) {
        this.jsonObject = jsonObject;
        this.models = new HashMap<>();
        this.initialize();
    }

    /**
     * 生成新实例
     *
     * @param jsonObject json数据
     * @return 新实例
     */
    public static StarumlFileTopModels newInstance(Object jsonObject) {
        return new StarumlFileTopModels(jsonObject);
    }

    private void initialize() {
        if (jsonObject instanceof Map) {
            Map jsonMap = (Map) jsonObject;
            if (jsonMap.containsKey(OWNED_ELEMENTS_KEY)) {
                Object elementsObject = jsonMap.get(OWNED_ELEMENTS_KEY);
                if (elementsObject instanceof List) {
                    for (Object item : (List) elementsObject) {
                        processSingleTopModel(item);
                    }
                }
            }
        }
    }

    private void processSingleTopModel(Object jsonObject) {
        if (jsonObject instanceof Map) {
            Map jsonMap = (Map) jsonObject;
            if (jsonMap.containsKey(UmlElement.ID_KEY)
                    && jsonMap.containsKey(UmlElement.TYPE_KEY)
                    && jsonMap.containsKey(UmlElement.NAME_KEY)) {
                String typeString = (String) jsonMap.get(UmlElement.TYPE_KEY);
                String name = (String) jsonMap.get(UmlElement.NAME_KEY);
                if (TopModelType.containsOriginalString(typeString)) {
                    TopModelType type = TopModelType.loadFromOriginalString(typeString);
                    setModel(type, name, jsonObject);
                }
            }
        }
    }

    private void setModel(TopModelType topModelType, String name, Object jsonObject) {
        this.models.put(new ModelKey(topModelType, name), jsonObject);
    }

    public Object getModel(TopModelType topModelType, String name) {
        ModelKey pair = new ModelKey(topModelType, name);
        return this.models.get(pair);
    }

    public boolean containsModel(TopModelType topModelType, String name) {
        ModelKey pair = new ModelKey(topModelType, name);
        return this.models.containsKey(pair);
    }

    public Set<ModelKey> getModelKeySet() {
        return this.models.keySet();
    }

    public int size() {
        return this.models.size();
    }

    public Object getJsonObject() {
        return jsonObject;
    }

    public static class ModelKey extends GenericPair<TopModelType, String> {
        private ModelKey(TopModelType topModelType, String name) {
            super(topModelType, name);
        }
    }
}
