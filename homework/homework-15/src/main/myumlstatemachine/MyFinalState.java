package main.myumlstatemachine;

import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlFinalState;

public class MyFinalState extends MyAllState {

    private Visibility visibility;

    public MyFinalState(UmlFinalState umlFinalState) {
        super(umlFinalState);

        this.visibility = umlFinalState.getVisibility();
    }

    public Visibility getVisibility() {
        return visibility;
    }
}
