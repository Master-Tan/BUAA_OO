package main;

import com.oocourse.uml2.models.common.NamedType;
import com.oocourse.uml2.models.common.ReferenceType;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlAttribute;

public class MyAttribute extends MyElement {

    private Visibility visibility;
    private String type;
    private String referenceId;
    private String typeName;

    public MyAttribute(UmlAttribute umlAttribute) {

        super(umlAttribute);

        this.visibility = umlAttribute.getVisibility();

        if (umlAttribute.getType() instanceof ReferenceType) {
            this.type = "ref";
            this.referenceId = ((ReferenceType)umlAttribute.getType()).getReferenceId();
            this.typeName = null;
        } else if (umlAttribute.getType() instanceof NamedType) {
            this.type = "name";
            this.typeName = ((NamedType)umlAttribute.getType()).getName();
            this.referenceId = null;
        }

    }

    public Visibility getVisibility() {
        return visibility;
    }

    public String getType() {
        return type;
    }

    public String getReferenceId() {
        return referenceId;
    }

    public String getTypeName() {
        return typeName;
    }
}
