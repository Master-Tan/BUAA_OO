package com.oocourse.uml1.models.top;

import com.oocourse.uml1.models.common.ElementType;
import com.oocourse.uml1.models.elements.UmlElement;
import com.oocourse.uml1.models.exceptions.UmlParseException;

import java.util.List;
import java.util.Map;

public abstract class StarumlModelWalker {
    private final Object jsonObject;

    public StarumlModelWalker(Object jsonObject) {
        this.jsonObject = jsonObject;
    }

    public abstract void umlElementEvent(UmlElement element);

    public abstract void parseErrorEvent(UmlParseException exception);

    private void walk(List jsonObject) {
        for (Object item : jsonObject) {
            walk(item);
        }
    }

    private void walk(Map jsonObject) {
        if (jsonObject.containsKey(UmlElement.TYPE_KEY)
                && jsonObject.containsKey(UmlElement.ID_KEY)) {
            String typeString = (String) jsonObject.get(UmlElement.TYPE_KEY);
            if (ElementType.containsOriginalString(typeString)) {
                UmlElement element = null;
                try {
                    element = UmlElement.loadFromJson(jsonObject);
                } catch (UmlParseException e) {
                    this.parseErrorEvent(e);
                }
                if (element != null) {
                    umlElementEvent(element);
                }
            }

            for (Object key : jsonObject.keySet()) {
                Object value = jsonObject.get(key);
                walk(value);
            }
        }
    }

    private void walk(Object jsonObject) {
        if (jsonObject instanceof Map) {
            walk((Map) jsonObject);
        } else if (jsonObject instanceof List) {
            walk((List) jsonObject);
        }
    }

    public void walk() {
        walk(this.jsonObject);
    }
}
