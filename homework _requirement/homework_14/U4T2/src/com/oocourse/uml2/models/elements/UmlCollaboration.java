package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.exceptions.UmlParseNotObjectException;

import java.util.Map;

public class UmlCollaboration extends UmlElement implements UmlClassOrInterface {
    protected UmlCollaboration(AbstractElementData elementData) {
        super(elementData);
    }

    public static UmlCollaboration loadFromJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }

        return new UmlCollaboration(elementData);
    }

    public static UmlCollaboration loadFromExportedJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }

        return new UmlCollaboration(elementData);
    }

    @Override
    public Visibility getVisibility() {
        return Visibility.PUBLIC;
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_COLLABORATION;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        if (!super.equals(o)) {
            return false;
        }
        UmlCollaboration that = (UmlCollaboration) o;
        return that.getName().equals(getName());
    }

    @Override
    public int hashCode() {
        return super.hashCode();
    }

    @Override
    public Map<String, Object> toJson() {
        return super.toJson();
    }
}
