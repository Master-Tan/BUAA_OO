package main.myumlclass;

import main.MyElement;
import com.oocourse.uml3.models.elements.UmlAssociation;

public class MyAssociation extends MyElement {

    private String end1;
    private String end2;

    public MyAssociation(UmlAssociation umlAssociation) {

        super(umlAssociation);

        this.end1 = umlAssociation.getEnd1();
        this.end2 = umlAssociation.getEnd2();

    }

    public String getEnd1() {
        return end1;
    }

    public String getEnd2() {
        return end2;
    }
}
