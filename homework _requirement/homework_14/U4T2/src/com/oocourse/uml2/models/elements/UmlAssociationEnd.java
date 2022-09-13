package com.oocourse.uml2.models.elements;

import com.oocourse.uml2.models.common.Aggregation;
import com.oocourse.uml2.models.common.ElementType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.exceptions.UmlParseKeyNotFoundException;
import com.oocourse.uml2.models.exceptions.UmlParseNotObjectException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public class UmlAssociationEnd extends UmlElement {
    private static final String VISIBILITY_KEY = "visibility";
    private static final String MULTIPLICITY_KEY = "multiplicity";
    private static final String REFERENCE_KEY = "reference";
    private static final String AGGREGATION_KEY = "aggregation";
    private final Visibility visibility;
    private final String multiplicity;
    private final String reference;
    private final Aggregation aggregation;

    private UmlAssociationEnd(AbstractElementData elementData, Visibility visibility, String multiplicity, String reference, Aggregation aggregation) {
        super(elementData);
        this.visibility = visibility;
        this.multiplicity = multiplicity;
        this.reference = reference;
        this.aggregation = aggregation;
    }

    public static UmlAssociationEnd loadFromJson(Object jsonObject) throws UmlParseException {
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

        String multiplicity;
        if (map.containsKey(MULTIPLICITY_KEY)) {
            Object value = map.get(MULTIPLICITY_KEY);
            multiplicity = (String) value;
        } else {
            multiplicity = "";
            // throw new UmlParseKeyNotFoundException(jsonObject, MULTIPLICITY_KEY);
        }

        String reference;
        if (map.containsKey(REFERENCE_KEY)) {
            Object value = map.get(REFERENCE_KEY);
            reference = loadReferenceDataFromJson(value).getReferenceId();
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, REFERENCE_KEY);
        }

        Aggregation aggregation;
        if (map.containsKey(AGGREGATION_KEY)) {
            Object value = map.get(AGGREGATION_KEY);
            aggregation = Aggregation.loadFromString((String) value);
        } else {
            aggregation = Aggregation.DEFAULT;
        }

        return new UmlAssociationEnd(elementData, visibility, multiplicity, reference, aggregation);
    }

    public static UmlAssociationEnd loadFromExportedJson(Object jsonObject) throws UmlParseException {
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

        String multiplicity;
        if (map.containsKey(MULTIPLICITY_KEY)) {
            Object value = map.get(MULTIPLICITY_KEY);
            multiplicity = (String) value;
        } else {
            multiplicity = null;
            // throw new UmlParseKeyNotFoundException(jsonObject, MULTIPLICITY_KEY);
        }

        String reference;
        if (map.containsKey(REFERENCE_KEY)) {
            Object value = map.get(REFERENCE_KEY);
            reference = (String) value;
        } else {
            throw new UmlParseKeyNotFoundException(jsonObject, REFERENCE_KEY);
        }

        Aggregation aggregation;
        if (map.containsKey(AGGREGATION_KEY)) {
            Object value = map.get(AGGREGATION_KEY);
            aggregation = Aggregation.loadFromString((String) value);
        } else {
            aggregation = Aggregation.DEFAULT;
        }

        return new UmlAssociationEnd(elementData, visibility, multiplicity, reference, aggregation);
    }

    @Override
    public ElementType getElementType() {
        return ElementType.UML_ASSOCIATION_END;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public String getMultiplicity() {
        return multiplicity;
    }

    public String getReference() {
        return reference;
    }

    public Aggregation getAggregation() {
        return aggregation;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        UmlAssociationEnd that = (UmlAssociationEnd) o;
        return visibility == that.visibility &&
                Objects.equals(multiplicity, that.multiplicity) &&
                Objects.equals(reference, that.reference) &&
                aggregation == that.aggregation;
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), visibility, multiplicity, reference, aggregation);
    }

    @Override
    public Map<String, Object> toJson() {
        Map<String, Object> result = super.toJson();
        result.putAll(new HashMap<String, Object>() {{
            put(VISIBILITY_KEY, visibility.getOriginalString());
            put(MULTIPLICITY_KEY, multiplicity);
            put(REFERENCE_KEY, reference);
            put(AGGREGATION_KEY, aggregation.getOriginalString());
        }});
        return result;
    }
}
