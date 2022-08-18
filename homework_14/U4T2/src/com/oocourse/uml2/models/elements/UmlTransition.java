package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.exceptions.UmlParseKeyNotFoundException;
import com.oocourse.uml2.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public class UmlTransition extends UmlElement {
    private static final String SOURCE_KEY = "source";
    private static final String TARGET_KEY = "target";
    private static final String VISIBILITY_KEY = "visibility";
    private static final String GUARD_KEY = "guard";
    private final String source;
    private final String target;
    private final Visibility visibility;
    private final String guard;

    private UmlTransition(AbstractElementData elementData, String source, String target, Visibility visibility, String guard) {
        super(elementData);
        this.source = source;
        this.target = target;
        this.visibility = visibility;
        this.guard = guard;
    }

    public static UmlTransition loadFromJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String source;
        if (map.containsKey(SOURCE_KEY)) {
            Object value = map.get(SOURCE_KEY);
            source = loadReferenceDataFromJson(value).getReferenceId();
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, SOURCE_KEY);
        }

        String target;
        if (map.containsKey(TARGET_KEY)) {
            Object value = map.get(TARGET_KEY);
            target = loadReferenceDataFromJson(value).getReferenceId();
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, TARGET_KEY);
        }

        Visibility visibility;
        if (map.containsKey(VISIBILITY_KEY)) {
            Object value = map.get(VISIBILITY_KEY);
            visibility = Visibility.loadFromString((String) value);
        } else {
            visibility = Visibility.DEFAULT;
        }

        String guard;
        if (map.containsKey(GUARD_KEY)) {
            Object value = map.get(GUARD_KEY);
            guard = (String) value;
        } else {
            guard = null;
        }

        return new UmlTransition(elementData, source, target, visibility, guard);
    }

    public static UmlTransition loadFromExportedJson(Object jsonObject) throws UmlParseException {
        AbstractElementData elementData = loadAbstractDataFromJson(jsonObject);
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String source;
        if (map.containsKey(SOURCE_KEY)) {
            Object value = map.get(SOURCE_KEY);
            source = (String) value;
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, SOURCE_KEY);
        }

        String target;
        if (map.containsKey(TARGET_KEY)) {
            Object value = map.get(TARGET_KEY);
            target = (String) value;
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, TARGET_KEY);
        }

        Visibility visibility;
        if (map.containsKey(VISIBILITY_KEY)) {
            Object value = map.get(VISIBILITY_KEY);
            visibility = Visibility.loadFromString((String) value);
        } else {
            visibility = Visibility.DEFAULT;
        }

        String guard;
        if (map.containsKey(GUARD_KEY)) {
            Object value = map.get(GUARD_KEY);
            guard = (String) value;
        } else {
            guard = null;
        }

        return new UmlTransition(elementData, source, target, visibility, guard);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(SOURCE_KEY, source);
            put(TARGET_KEY, target);
            put(VISIBILITY_KEY, visibility.getOriginalString());
            put(GUARD_KEY, guard);
        }});
        return result;
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_TRANSITION;
    }

    public String getSource() {
        return source;
    }

    public String getTarget() {
        return target;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public String getGuard() {
        return guard;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlTransition that = (UmlTransition) o;
        return Objects.equals(source, that.source) &&
                Objects.equals(target, that.target) &&
                visibility == that.visibility &&
                Objects.equals(guard, that.guard);
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), source, target, visibility, guard);
    }
}
