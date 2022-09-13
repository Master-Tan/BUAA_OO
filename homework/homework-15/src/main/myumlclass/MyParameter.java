package main.myumlclass;

import main.MyElement;
import com.oocourse.uml3.models.common.Direction;
import com.oocourse.uml3.models.common.NamedType;
import com.oocourse.uml3.models.common.ReferenceType;
import com.oocourse.uml3.models.elements.UmlParameter;

public class MyParameter extends MyElement {

    private String type;
    private String referenceId;
    private String typeName;
    private Direction direction;

    public MyParameter(UmlParameter umlParameter) {

        super(umlParameter);

        if (umlParameter.getType() instanceof ReferenceType) {
            this.type = "ref";
            this.referenceId = ((ReferenceType)umlParameter.getType()).getReferenceId();
            this.typeName = null;
        } else if (umlParameter.getType() instanceof NamedType) {
            this.type = "name";
            this.typeName = ((NamedType)umlParameter.getType()).getName();
            this.referenceId = null;
        }
        this.direction = umlParameter.getDirection();

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

    public Direction getDirection() {
        return direction;
    }
}
