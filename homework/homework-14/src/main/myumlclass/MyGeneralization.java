package main.myumlclass;

import main.MyElement;
import com.oocourse.uml2.models.elements.UmlGeneralization;

public class MyGeneralization extends MyElement {

    private String sourse;
    private String target;

    public MyGeneralization(UmlGeneralization umlGeneralization) {

        super(umlGeneralization);

        this.sourse = umlGeneralization.getSource();
        this.target = umlGeneralization.getTarget();

    }

    public String getSourse() {
        return sourse;
    }

    public String getTarget() {
        return target;
    }
}
