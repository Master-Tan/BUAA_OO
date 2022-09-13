package main.myumlstatemachine;

import main.MyElement;
import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlEvent;

public class MyEvent extends MyElement {

    private Visibility visibility;
    private String expression;
    private String values;

    public MyEvent(UmlEvent umlEvent) {
        super(umlEvent);

        this.visibility = umlEvent.getVisibility();
        this.expression = umlEvent.getExpression();
        this.values = umlEvent.getValue();
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public String getExpression() {
        return expression;
    }

    public String getValues() {
        return values;
    }
}
