package main.myumlstatemachine;

import main.MyElement;
import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlRegion;

import java.util.HashMap;

public class MyRegion extends MyElement {

    private HashMap<String, MyPseudostate> pseudostates = new HashMap<>();
    private HashMap<String, MyState> states = new HashMap<>();
    private HashMap<String, MyFinalState> finalStates = new HashMap<>();
    private HashMap<String, MyTransition> transitions = new HashMap<>();
    private HashMap<String, MyAllState> allStates = new HashMap<>();

    private Visibility visibility;

    public MyRegion(UmlRegion umlRegion) {
        super(umlRegion);

        this.visibility = umlRegion.getVisibility();
    }

    public void addPseudoStates(MyPseudostate myPseudostate) {
        pseudostates.put(myPseudostate.getId(), myPseudostate);
        allStates.put(myPseudostate.getId(), myPseudostate);
    }

    public void addStates(MyState myState) {
        states.put(myState.getId(), myState);
        allStates.put(myState.getId(), myState);
    }

    public void addFinalStates(MyFinalState myFinalState) {
        finalStates.put(myFinalState.getId(), myFinalState);
        allStates.put(myFinalState.getId(), myFinalState);
    }

    public void addTransitions(MyTransition myTransition) {
        transitions.put(myTransition.getId(), myTransition);
    }

    public HashMap<String, MyPseudostate> getPseudostates() {
        return pseudostates;
    }

    public HashMap<String, MyState> getStates() {
        return states;
    }

    public HashMap<String, MyFinalState> getFinalStates() {
        return finalStates;
    }

    public HashMap<String, MyTransition> getTransitions() {
        return transitions;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public HashMap<String, MyAllState> getAllStates() {
        return allStates;
    }
}
