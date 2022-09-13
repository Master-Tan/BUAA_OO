package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.exceptions.UmlParseKeyNotFoundException;
import com.oocourse.uml2.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public class UmlInterfaceRealization extends UmlElement {
    private static final String SOURCE_KEY = "source";
    private static final String TARGET_KEY = "target";
    private final String source;
    private final String target;

    private UmlInterfaceRealization(AbstractElementData elementData, String source, String target) {
        super(elementData);
        this.source = source;
        this.target = target;
    }

    public static UmlInterfaceRealization loadFromJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String source;
        if (map.containsKey(SOURCE_KEY)) {
            Object value = map.get(SOURCE_KEY);
            source = loadReferenceDataFromJson(value).getReferenceId();
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, SOURCE_KEY);
        }

        String target;
        if (map.containsKey(TARGET_KEY)) {
            Object value = map.get(TARGET_KEY);
            target = loadReferenceDataFromJson(value).getReferenceId();
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, TARGET_KEY);
        }

        return new UmlInterfaceRealization(elementData, source, target);
    }

    public static UmlInterfaceRealization loadFromExportedJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String source;
        if (map.containsKey(SOURCE_KEY)) {
            Object value = map.get(SOURCE_KEY);
            source = (String) value;
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, SOURCE_KEY);
        }

        String target;
        if (map.containsKey(TARGET_KEY)) {
            Object value = map.get(TARGET_KEY);
            target = (String) value;
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, TARGET_KEY);
        }

        return new UmlInterfaceRealization(elementData, source, target);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_INTERFACE_REALIZATION;
    }

    public String getSource() {
        return source;
    }

    public String getTarget() {
        return target;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlInterfaceRealization that = (UmlInterfaceRealization) o;
        return Objects.equals(source, that.source) &&
                Objects.equals(target, that.target);
    }

    @Override
    public int hashCode() {

        return Objects.hash(super.hashCode(), source, target);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(SOURCE_KEY, source);
            put(TARGET_KEY, target);
        }});
        return result;
    }
}
