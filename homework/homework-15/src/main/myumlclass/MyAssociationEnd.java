package main.myumlclass;

import com.oocourse.uml3.models.common.Aggregation;
import com.oocourse.uml3.models.common.Visibility;
import main.MyElement;
import com.oocourse.uml3.models.elements.UmlAssociationEnd;

public class MyAssociationEnd extends MyElement {

    private Visibility visibility;
    private String reference;
    private String multiplicity;
    private Aggregation aggregation;

    public MyAssociationEnd(UmlAssociationEnd umlAssociationEnd) {

        super(umlAssociationEnd);

        this.visibility = umlAssociationEnd.getVisibility();
        this.reference = umlAssociationEnd.getReference();
        this.multiplicity = umlAssociationEnd.getMultiplicity();
        this.aggregation = umlAssociationEnd.getAggregation();
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public String getReference() {
        return reference;
    }

    public String getMultiplicity() {
        return multiplicity;
    }

    public Aggregation getAggregation() {
        return aggregation;
    }
}
