package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.MessageSort;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.exceptions.UmlParseKeyNotFoundException;
import com.oocourse.uml2.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

@SuppressWarnings("Duplicates")
public class UmlMessage extends UmlElement {
    private static final String VISIBILITY_KEY = "visibility";
    private static final String SOURCE_KEY = "source";
    private static final String TARGET_KEY = "target";
    private static final String MESSAGE_SORT_KEY = "messageSort";
    private final Visibility visibility;
    private final String source;
    private final String target;
    private final MessageSort messageSort;

    private UmlMessage(AbstractElementData elementData, Visibility visibility, String source, String target, MessageSort messageSort) {
        super(elementData);
        this.visibility = visibility;
        this.source = source;
        this.target = target;
        this.messageSort = messageSort;
    }

    public static UmlMessage loadFromJson(Object jsonObject) throws UmlParseException {
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

        MessageSort messageSort;
        if (map.containsKey(MESSAGE_SORT_KEY)) {
            Object value = map.get(MESSAGE_SORT_KEY);
            messageSort = MessageSort.loadFromString((String) value);
        } else {
            messageSort = MessageSort.DEFAULT;
        }

        return new UmlMessage(elementData, visibility, source, target, messageSort);
    }

    public static UmlMessage loadFromExportedJson(Object jsonObject) throws UmlParseException {
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

        MessageSort messageSort;
        if (map.containsKey(MESSAGE_SORT_KEY)) {
            Object value = map.get(MESSAGE_SORT_KEY);
            messageSort = MessageSort.loadFromString((String) value);
        } else {
            messageSort = MessageSort.DEFAULT;
        }

        return new UmlMessage(elementData, visibility, source, target, messageSort);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_MESSAGE;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public String getSource() {
        return source;
    }

    public String getTarget() {
        return target;
    }

    public MessageSort getMessageSort() {
        return messageSort;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlMessage that = (UmlMessage) o;
        return visibility == that.visibility &&
                Objects.equals(source, that.source) &&
                Objects.equals(target, that.target) &&
                messageSort == that.messageSort;
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), visibility, source, target, messageSort);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(VISIBILITY_KEY, visibility.getOriginalString());
            put(SOURCE_KEY, source);
            put(TARGET_KEY, target);
            put(MESSAGE_SORT_KEY, messageSort.getOriginalString());
        }});
        return result;
    }
}
