package main.myumlstatemachine;

import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlPseudostate;

public class MyPseudostate extends MyAllState {

    private Visibility visibility;

    public MyPseudostate(UmlPseudostate umlPseudostate) {
        super(umlPseudostate);

        this.visibility = umlPseudostate.getVisibility();
    }

    public Visibility getVisibility() {
        return visibility;
    }
}
