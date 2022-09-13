package main.myumlstatemachine;

import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlState;

public class MyState extends MyAllState {

    private Visibility visibility;

    public MyState(UmlState umlState) {
        super(umlState);

        this.visibility = umlState.getVisibility();
    }

    public Visibility getVisibility() {
        return visibility;
    }
}
