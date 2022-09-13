package com.oocourse.uml1.models.elements;

import com.oocourse.uml1.models.common.ElementType;
import com.oocourse.uml1.models.common.Visibility;
import com.oocourse.uml1.models.exceptions.UmlParseException;
import com.oocourse.uml1.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

@SuppressWarnings({"unchecked", "Duplicates"})
public class UmlClass extends UmlElement {
    private static final String VISIBILITY_KEY = "visibility";
    private final Visibility visibility;

    private UmlClass(AbstractElementData elementData, Visibility visibility) {
        super(elementData);
        this.visibility = visibility;
    }

    public static UmlClass loadFromJson(Object jsonObject) throws UmlParseException {
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

        return new UmlClass(elementData, visibility);
    }

    public static UmlClass loadFromExportedJson(Object jsonObject) throws UmlParseException {
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

        return new UmlClass(elementData, visibility);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_CLASS;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlClass umlClass = (UmlClass) o;
        return visibility == umlClass.visibility;
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), visibility);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(VISIBILITY_KEY, visibility.toLowerCaseString());
        }});
        return result;
    }
}
