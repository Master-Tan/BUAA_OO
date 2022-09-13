package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

@SuppressWarnings("Duplicates")
public class UmlEvent extends UmlElement {
    private static final String VALUE_KEY = "value";
    private static final String EXPRESSION_KEY = "expression";
    private static final String VISIBILITY_KEY = "visibility";
    private final String value;
    private final String expression;
    private final Visibility visibility;

    private UmlEvent(AbstractElementData elementData, String value, String expression, Visibility visibility) {
        super(elementData);
        this.value = value;
        this.expression = expression;
        this.visibility = visibility;
    }

    public static UmlEvent loadFromJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String valueResult;
        if (map.containsKey(VALUE_KEY)) {
            Object value = map.get(VALUE_KEY);
            valueResult = (String) value;
        } else {
            valueResult = null;
        }

        String expression;
        if (map.containsKey(EXPRESSION_KEY)) {
            Object value = map.get(EXPRESSION_KEY);
            expression = (String) value;
        } else {
            expression = null;
        }

        Visibility visibility;
        if (map.containsKey(VISIBILITY_KEY)) {
            Object value = map.get(VISIBILITY_KEY);
            visibility = Visibility.loadFromString((String) value);
        } else {
            visibility = Visibility.DEFAULT;
        }

        return new UmlEvent(elementData, valueResult, expression, visibility);
    }

    public static UmlEvent loadFromExportedJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String valueResult;
        if (map.containsKey(VALUE_KEY)) {
            Object value = map.get(VALUE_KEY);
            valueResult = (String) value;
        } else {
            valueResult = null;
        }

        String expression;
        if (map.containsKey(EXPRESSION_KEY)) {
            Object value = map.get(EXPRESSION_KEY);
            expression = (String) value;
        } else {
            expression = null;
        }

        Visibility visibility;
        if (map.containsKey(VISIBILITY_KEY)) {
            Object value = map.get(VISIBILITY_KEY);
            visibility = Visibility.loadFromString((String) value);
        } else {
            visibility = Visibility.DEFAULT;
        }

        return new UmlEvent(elementData, valueResult, expression, visibility);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(VALUE_KEY, value);
            put(EXPRESSION_KEY, expression);
            put(VISIBILITY_KEY, visibility.getOriginalString());
        }});
        return result;
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_EVENT;
    }

    public String getValue() {
        return value;
    }

    public String getExpression() {
        return expression;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlEvent umlEvent = (UmlEvent) o;
        return Objects.equals(value, umlEvent.value) &&
                Objects.equals(expression, umlEvent.expression) &&
                visibility == umlEvent.visibility;
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), value, expression, visibility);
    }
}
