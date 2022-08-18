package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.exceptions.UmlParseKeyNotFoundException;
import com.oocourse.uml2.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

@SuppressWarnings("Duplicates")
public class UmlLifeline extends UmlElement {
    private static final String VISIBILITY_KEY = "visibility";
    private static final String REPRESENT_KEY = "represent";
    private static final String IS_MULTI_INSTANCE_KEY = "isMultiInstance";
    private static final boolean DEFAULT_IS_MULTI_INSTANCE = false;
    private final Visibility visibility;
    private final String represent;
    private final boolean isMultiInstance;

    private UmlLifeline(AbstractElementData elementData, Visibility visibility, String represent, boolean isMultiInstance) {
        super(elementData);
        this.visibility = visibility;
        this.represent = represent;
        this.isMultiInstance = isMultiInstance;
    }

    public static UmlLifeline loadFromJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        Visibility visibility;
        if (map.containsKey(VISIBILITY_KEY)) {
            Object value = map.get(VISIBILITY_KEY);
            visibility = Visibility.loadFromString((String) value);
        } else {
            visibility = Visibility.DEFAULT;
        }

        String represent;
        if (map.containsKey(REPRESENT_KEY)) {
            Object value = map.get(REPRESENT_KEY);
            represent = loadReferenceDataFromJson(value).getReferenceId();
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, REPRESENT_KEY);
        }

        boolean isMultiInstance;
        if (map.containsKey(IS_MULTI_INSTANCE_KEY)) {
            Object value = map.get(IS_MULTI_INSTANCE_KEY);
            isMultiInstance = (boolean) value;
        } else {
            isMultiInstance = DEFAULT_IS_MULTI_INSTANCE;
        }

        return new UmlLifeline(elementData, visibility, represent, isMultiInstance);
    }

    public static UmlLifeline loadFromExportedJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        Visibility visibility;
        if (map.containsKey(VISIBILITY_KEY)) {
            Object value = map.get(VISIBILITY_KEY);
            visibility = Visibility.loadFromString((String) value);
        } else {
            visibility = Visibility.DEFAULT;
        }

        String represent;
        if (map.containsKey(REPRESENT_KEY)) {
            Object value = map.get(REPRESENT_KEY);
            represent = (String) value;
        } else {
            represent = null;
        }

        boolean isMultiInstance;
        if (map.containsKey(IS_MULTI_INSTANCE_KEY)) {
            Object value = map.get(IS_MULTI_INSTANCE_KEY);
            isMultiInstance = (boolean) value;
        } else {
            isMultiInstance = DEFAULT_IS_MULTI_INSTANCE;
        }

        return new UmlLifeline(elementData, visibility, represent, isMultiInstance);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_LIFELINE;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public String getRepresent() {
        return represent;
    }

    public boolean isMultiInstance() {
        return isMultiInstance;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlLifeline that = (UmlLifeline) o;
        return isMultiInstance == that.isMultiInstance &&
                visibility == that.visibility &&
                Objects.equals(represent, that.represent);
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), visibility, represent, isMultiInstance);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(VISIBILITY_KEY, visibility.getOriginalString());
            put(REPRESENT_KEY, represent);
            put(IS_MULTI_INSTANCE_KEY, isMultiInstance);
        }});
        return result;
    }
}
