package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.utils.json.OutputWithJson;

import java.util.Map;

public interface UmlElementInterface extends OutputWithJson<Map<String, Object>> {
    ElementType getElementType();

    String getId();

    String getName();

    String getParentId();
}
