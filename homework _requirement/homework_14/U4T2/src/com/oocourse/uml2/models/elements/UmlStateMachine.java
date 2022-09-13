package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.exceptions.UmlParseNotObjectException;

import java.util.Map;

public class UmlStateMachine extends UmlElement {
    private UmlStateMachine(AbstractElementData elementData) {
        super(elementData);
    }

    public static UmlStateMachine loadFromJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }

        return new UmlStateMachine(elementData);
    }

    public static UmlStateMachine loadFromExportedJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }

        return new UmlStateMachine(elementData);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_STATE_MACHINE;
    }

    @Override
    public Map<String, Object> toJson() {
        return super.toJson();
    }
}
