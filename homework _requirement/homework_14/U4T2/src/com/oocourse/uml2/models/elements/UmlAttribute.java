package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.NameableType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.exceptions.UmlParseKeyNotFoundException;
import com.oocourse.uml2.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

@SuppressWarnings("Duplicates")
public class UmlAttribute extends UmlElement {
    private static final String VISIBILITY_KEY = "visibility";
    private static final String TYPE_KEY = "type";
    private final Visibility visibility;
    private final NameableType type;

    private UmlAttribute(AbstractElementData elementData, Visibility visibility, NameableType type) {
        super(elementData);
        this.visibility = visibility;
        this.type = type;
    }

    public static UmlAttribute loadFromJson(Object jsonObject) throws UmlParseException {
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

        NameableType type;
        if (map.containsKey(TYPE_KEY)) {
            Object value = map.get(TYPE_KEY);
            type = NameableType.loadFromJson(value);
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, TYPE_KEY);
        }

        return new UmlAttribute(elementData, visibility, type);
    }

    public static UmlAttribute loadFromExportedJson(Object jsonObject) throws UmlParseException {
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

        NameableType type;
        if (map.containsKey(TYPE_KEY)) {
            Object value = map.get(TYPE_KEY);
            type = NameableType.loadFromJson(value);
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, TYPE_KEY);
        }

        return new UmlAttribute(elementData, visibility, type);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_ATTRIBUTE;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public NameableType getType() {
        return type;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlAttribute that = (UmlAttribute) o;
        return visibility == that.visibility &&
                Objects.equals(type, that.type);
    }

    @Override
    public int hashCode() {

        return Objects.hash(super.hashCode(), visibility, type);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(VISIBILITY_KEY, visibility.getOriginalString());
            put(TYPE_KEY, type.toJson());
        }});
        return result;
    }
}
