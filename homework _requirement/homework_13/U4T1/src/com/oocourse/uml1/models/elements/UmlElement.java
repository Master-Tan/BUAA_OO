package com.oocourse.uml1.models.elements;

import com.oocourse.uml1.models.common.ElementType;
import com.oocourse.uml1.models.exceptions.UmlParseElementTypeNotSupportedException;
import com.oocourse.uml1.models.exceptions.UmlParseException;
import com.oocourse.uml1.models.exceptions.UmlParseKeyNotFoundException;
import com.oocourse.uml1.models.exceptions.UmlParseNotArrayException;
import com.oocourse.uml1.models.exceptions.UmlParseNotObjectException;
import com.oocourse.uml1.utils.json.InputWithJson;
import com.oocourse.uml1.utils.json.OutputWithJson;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

@SuppressWarnings({"WeakerAccess", "Duplicates"})
public abstract class UmlElement implements OutputWithJson<Map<String, Object>> {
    public static final String REF_KEY = "$ref";
    public static final String ID_KEY = "_id";
    public static final String NAME_KEY = "name";
    public static final String PARENT_KEY = "_parent";
    public static final String TYPE_KEY = "_type";
    private static final Map<ElementType, InputWithJson<? extends UmlElement, UmlParseException>> JSON_LOAD_RELATION =
            Collections.unmodifiableMap(new HashMap<ElementType, InputWithJson<? extends UmlElement, UmlParseException>>() {{
                put(ElementType.UML_CLASS, UmlClass::loadFromJson);
                put(ElementType.UML_ATTRIBUTE, UmlAttribute::loadFromJson);
                put(ElementType.UML_OPERATION, UmlOperation::loadFromJson);
                put(ElementType.UML_PARAMETER, UmlParameter::loadFromJson);
                put(ElementType.UML_ASSOCIATION, UmlAssociation::loadFromJson);
                put(ElementType.UML_ASSOCIATION_END, UmlAssociationEnd::loadFromJson);
                put(ElementType.UML_GENERALIZATION, UmlGeneralization::loadFromJson);
                put(ElementType.UML_INTERFACE_REALIZATION, UmlInterfaceRealization::loadFromJson);
                put(ElementType.UML_INTERFACE, UmlInterface::loadFromJson);
            }});
    private static final Map<ElementType, InputWithJson<? extends UmlElement, UmlParseException>> JSON_EXPORTED_LOAD_RELATION =
            Collections.unmodifiableMap(new HashMap<ElementType, InputWithJson<? extends UmlElement, UmlParseException>>() {{
                put(ElementType.UML_CLASS, UmlClass::loadFromExportedJson);
                put(ElementType.UML_ATTRIBUTE, UmlAttribute::loadFromExportedJson);
                put(ElementType.UML_OPERATION, UmlOperation::loadFromExportedJson);
                put(ElementType.UML_PARAMETER, UmlParameter::loadFromExportedJson);
                put(ElementType.UML_ASSOCIATION, UmlAssociation::loadFromExportedJson);
                put(ElementType.UML_ASSOCIATION_END, UmlAssociationEnd::loadFromExportedJson);
                put(ElementType.UML_GENERALIZATION, UmlGeneralization::loadFromExportedJson);
                put(ElementType.UML_INTERFACE_REALIZATION, UmlInterfaceRealization::loadFromExportedJson);
                put(ElementType.UML_INTERFACE, UmlInterface::loadFromExportedJson);
            }});
    private final String id;
    private final String name;
    private final String parentId;

    private UmlElement(String id, String parentId, String name) {
        this.id = id;
        this.parentId = parentId;
        this.name = name;
    }

    protected UmlElement(AbstractElementData elementData) {
        this(elementData.getId(), elementData.getParentId(), elementData.getName());
    }

    protected static AbstractElementData loadAbstractDataFromJson(Object jsonObject)
            throws UmlParseException {
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String id;
        if (map.containsKey(ID_KEY)) {
            Object value = map.get(ID_KEY);
            id = (String) value;
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, ID_KEY);
        }

        String name;
        if (map.containsKey(NAME_KEY)) {
            Object value = map.get(NAME_KEY);
            name = (String) value;
        } else {
            name = null;
        }

        String parentId;
        if (map.containsKey(PARENT_KEY)) {
            Object value = map.get(PARENT_KEY);
            if (value instanceof Map) {
                parentId = loadReferenceDataFromJson(value).getReferenceId();
            } else {
                parentId = (String) value;
            }
        } else {
            parentId = null;
        }

        return new AbstractElementData(id, parentId, name);
    }

    private static AbstractReferenceData loadAbstractReferenceDataFromJson(Object jsonObject, String key)
            throws UmlParseException {
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        String referenceId;
        if (map.containsKey(key)) {
            Object value = map.get(key);
            referenceId = (String) value;
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, key);
        }

        return new AbstractReferenceData(referenceId);
    }

    protected static AbstractReferenceData loadReferenceDataFromJson(Object jsonObject)
            throws UmlParseException {
        return loadAbstractReferenceDataFromJson(jsonObject, REF_KEY);
    }

    protected static AbstractReferenceData loadElementReferenceDataFromJson(Object jsonObject)
            throws UmlParseException {
        return loadAbstractReferenceDataFromJson(jsonObject, ID_KEY);
    }

    protected static List<String> loadAbstractReferenceListFromJson(Object jsonObject, ObjectToString transformer)
            throws UmlParseException {
        if (jsonObject instanceof List) {
            ArrayList<String> list = new ArrayList<>();
            for (Object item : (List) jsonObject) {
                list.add(transformer.transform(item));
            }
            return list;
        } else {
            throw new UmlParseNotArrayException(jsonObject);
        }
    }

    protected static List<String> loadReferenceListFromJson(Object jsonObject) throws UmlParseException {
        return loadAbstractReferenceListFromJson(jsonObject,
                (Object o) -> loadReferenceDataFromJson(o).getReferenceId());
    }

    protected static List<String> loadElementReferenceListFromJson(Object jsonObject) throws UmlParseException {
        return loadAbstractReferenceListFromJson(jsonObject,
                (Object o) -> loadElementReferenceDataFromJson(o).getReferenceId());
    }

    public static boolean isElement(Object jsonObject) {
        if (!(jsonObject instanceof Map)) {
            return false;
        }
        Map map = (Map) jsonObject;

        if (map.containsKey(TYPE_KEY)) {
            Object value = map.get(TYPE_KEY);
            return ElementType.containsOriginalString((String) value);
        } else {
            return false;
        }
    }

    private static ElementType getElementTypeFromJson(Object jsonObject) throws UmlParseException {
        if (!(jsonObject instanceof Map)) {
            throw new UmlParseNotObjectException(jsonObject);
        }
        Map map = (Map) jsonObject;

        ElementType type;
        if (map.containsKey(TYPE_KEY)) {
            Object value = map.get(TYPE_KEY);
            type = ElementType.loadFromOriginalString((String) value);
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, TYPE_KEY);
        }

        return type;
    }

    public static UmlElement loadFromJson(Object jsonObject) throws UmlParseException {
        ElementType type = getElementTypeFromJson(jsonObject);
        if (JSON_LOAD_RELATION.containsKey(type)) {
            InputWithJson<? extends UmlElement, UmlParseException> inputWithJson
                    = JSON_LOAD_RELATION.get(type);
            return inputWithJson.loadFromJson(jsonObject);
        } else {
            throw new UmlParseElementTypeNotSupportedException(jsonObject, type);
        }
    }

    public static UmlElement loadFromExportedJson(Object jsonObject) throws UmlParseException {
        ElementType type = getElementTypeFromJson(jsonObject);
        if (JSON_EXPORTED_LOAD_RELATION.containsKey(type)) {
            InputWithJson<? extends UmlElement, UmlParseException> inputWithJson
                    = JSON_EXPORTED_LOAD_RELATION.get(type);
            return inputWithJson.loadFromJson(jsonObject);
        } else {
            throw new UmlParseElementTypeNotSupportedException(jsonObject, type);
        }
    }

    public abstract ElementType getElementType();

    public String getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public String getParentId() {
        return parentId;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        UmlElement that = (UmlElement) o;
        return Objects.equals(id, that.id) &&
                Objects.equals(name, that.name) &&
                Objects.equals(parentId, that.parentId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(id, name, parentId);
    }

    public Map<String, Object> toJson() {
        return new HashMap<String, Object>() {{
            put(ID_KEY, id);
            put(PARENT_KEY, parentId);
            put(NAME_KEY, name);
            put(TYPE_KEY, getElementType().getOriginalString());
        }};
    }

    /**
     * 获取字符串形式
     *
     * @return 字符串形式
     */
    @Override
    public String toString() {
        if (this.getName() != null) {
            return String.format("<%s name: %s, id: %s>", this.getClass().getSimpleName(), getName(), getId());
        } else {
            return String.format("<%s id: %s>", this.getClass().getSimpleName(), getId());
        }
    }

    private interface ObjectToString {
        String transform(Object o) throws UmlParseException;
    }

    @SuppressWarnings("WeakerAccess")
    protected static class AbstractElementData {
        private final String name;
        private final String id;
        private final String parentId;

        private AbstractElementData(String id, String parentId, String name) {
            this.id = id;
            this.parentId = parentId;
            this.name = name;
        }

        public String getName() {
            return name;
        }

        public String getId() {
            return id;
        }

        public String getParentId() {
            return parentId;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            AbstractElementData that = (AbstractElementData) o;
            return Objects.equals(name, that.name) &&
                    Objects.equals(id, that.id) &&
                    Objects.equals(parentId, that.parentId);
        }

        @Override
        public int hashCode() {

            return Objects.hash(name, id, parentId);
        }
    }

    @SuppressWarnings("WeakerAccess")
    protected static class AbstractReferenceData {
        private final String referenceId;

        private AbstractReferenceData(String referenceId) {
            this.referenceId = referenceId;
        }

        public String getReferenceId() {
            return referenceId;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            AbstractReferenceData that = (AbstractReferenceData) o;
            return Objects.equals(referenceId, that.referenceId);
        }

        @Override
        public int hashCode() {

            return Objects.hash(referenceId);
        }
    }
}
