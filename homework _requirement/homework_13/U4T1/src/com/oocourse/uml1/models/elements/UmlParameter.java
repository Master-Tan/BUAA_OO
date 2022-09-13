package com.oocourse.uml1.models.elements;

import com.oocourse.uml1.models.common.Direction;
import com.oocourse.uml1.models.common.ElementType;
import com.oocourse.uml1.models.common.NameableType;
import com.oocourse.uml1.models.exceptions.UmlParseException;
import com.oocourse.uml1.models.exceptions.UmlParseKeyNotFoundException;
import com.oocourse.uml1.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

@SuppressWarnings("Duplicates")
public class UmlParameter extends UmlElement {
    private static final String DIRECTION_KEY = "direction";
    private static final String TYPE_KEY = "type";
    private final Direction direction;
    private final NameableType type;

    private UmlParameter(AbstractElementData elementData, Direction direction, NameableType type) {
        super(elementData);
        this.direction = direction;
        this.type = type;
    }

    public static UmlParameter loadFromJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        Direction direction;
        if (map.containsKey(DIRECTION_KEY)) {
            Object value = map.get(DIRECTION_KEY);
            direction = Direction.loadFromString((String) value);
        } else {
            direction = Direction.DEFAULT;
        }

        NameableType type;
        if (map.containsKey(TYPE_KEY)) {
            Object value = map.get(TYPE_KEY);
            type = NameableType.loadFromJson(value);
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, TYPE_KEY);
        }

        return new UmlParameter(elementData, direction, type);
    }

    public static UmlParameter loadFromExportedJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        Direction direction;
        if (map.containsKey(DIRECTION_KEY)) {
            Object value = map.get(DIRECTION_KEY);
            direction = Direction.loadFromString((String) value);
        } else {
            direction = Direction.DEFAULT;
        }

        NameableType type;
        if (map.containsKey(TYPE_KEY)) {
            Object value = map.get(TYPE_KEY);
            type = NameableType.loadFromJson(value);
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, TYPE_KEY);
        }

        return new UmlParameter(elementData, direction, type);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_PARAMETER;
    }

    public Direction getDirection() {
        return direction;
    }

    public NameableType getType() {
        return type;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlParameter that = (UmlParameter) o;
        return direction == that.direction &&
                Objects.equals(type, that.type);
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), direction, type);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(DIRECTION_KEY, direction.toLowerCaseString());
            put(TYPE_KEY, type.toJson());
        }});
        return result;
    }
}
