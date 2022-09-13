package main.myumlstatemachine;

import com.oocourse.uml3.models.elements.UmlElement;
import main.MyElement;

import java.util.HashMap;

public class MyAllState extends MyElement {

    private HashMap<String, MyAllState> nextStates = new HashMap<>();
    private HashMap<String, MyTransition> outTransition = new HashMap<>();

    public MyAllState(UmlElement umlElement) {
        super(umlElement);
    }

    public void addTransition(MyTransition myTransition, MyAllState myAllState) {
        outTransition.put(myTransition.getId(), myTransition);
        nextStates.put(myAllState.getId(), myAllState);
    }

    public HashMap<String, MyAllState> getNextStates() {
        return nextStates;
    }

    public HashMap<String, MyTransition> getOutTransition() {
        return outTransition;
    }
}
