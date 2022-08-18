package com.oocourse.uml1.models.elements;

import com.oocourse.uml1.models.common.ElementType;
import com.oocourse.uml1.models.common.Visibility;
import com.oocourse.uml1.models.exceptions.UmlParseException;
import com.oocourse.uml1.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

@SuppressWarnings({"unchecked", "Duplicates"})
public class UmlInterface extends UmlElement {
    private static final String VISIBILITY_KEY = "visibility";
    private static final String OPERATIONS_KEY = "operations";
    private final Visibility visibility;

    private UmlInterface(AbstractElementData elementData, Visibility visibility) {
        super(elementData);
        this.visibility = visibility;
    }

    public static UmlInterface loadFromJson(Object jsonObject) throws UmlParseException {
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

        return new UmlInterface(elementData, visibility);
    }

    public static UmlInterface loadFromExportedJson(Object jsonObject) throws UmlParseException {
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

        return new UmlInterface(elementData, visibility);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_INTERFACE;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlInterface that = (UmlInterface) o;
        return visibility == that.visibility;
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
