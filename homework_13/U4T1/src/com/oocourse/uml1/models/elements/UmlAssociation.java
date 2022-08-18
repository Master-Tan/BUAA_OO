package com.oocourse.uml1.models.elements;

import com.oocourse.uml1.models.common.ElementType;
import com.oocourse.uml1.models.exceptions.UmlParseException;
import com.oocourse.uml1.models.exceptions.UmlParseKeyNotFoundException;
import com.oocourse.uml1.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public class UmlAssociation extends UmlElement {
    private static final String END1_KEY = "end1";
    private static final String END2_KEY = "end2";
    private final String end1;
    private final String end2;

    private UmlAssociation(AbstractElementData elementData, String end1, String end2) {
        super(elementData);
        this.end1 = end1;
        this.end2 = end2;
    }

    public static UmlAssociation loadFromJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String end1;
        if (map.containsKey(END1_KEY)) {
            Object value = map.get(END1_KEY);
            end1 = loadElementReferenceDataFromJson(value).getReferenceId();
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, END1_KEY);
        }

        String end2;
        if (map.containsKey(END2_KEY)) {
            Object value = map.get(END2_KEY);
            end2 = loadElementReferenceDataFromJson(value).getReferenceId();
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, END2_KEY);
        }

        return new UmlAssociation(elementData, end1, end2);
    }

    public static UmlAssociation loadFromExportedJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String end1;
        if (map.containsKey(END1_KEY)) {
            Object value = map.get(END1_KEY);
            end1 = (String) value;
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, END1_KEY);
        }

        String end2;
        if (map.containsKey(END2_KEY)) {
            Object value = map.get(END2_KEY);
            end2 = (String) value;
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, END2_KEY);
        }

        return new UmlAssociation(elementData, end1, end2);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_ASSOCIATION;
    }

    public String getEnd1() {
        return end1;
    }

    public String getEnd2() {
        return end2;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlAssociation that = (UmlAssociation) o;
        return Objects.equals(end1, that.end1) &&
                Objects.equals(end2, that.end2);
    }

    @Override
    public int hashCode() {

        return Objects.hash(super.hashCode(), end1, end2);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(END1_KEY, end1);
            put(END2_KEY, end2);
        }});
        return result;
    }
}
