package main.myumlstatemachine;

import com.oocourse.uml2.models.elements.UmlElement;
import main.MyElement;

import java.util.HashMap;

public class MyAllState extends MyElement {

    private HashMap<String, MyAllState> nextStates = new HashMap<>();

    public MyAllState(UmlElement umlElement) {
        super(umlElement);
    }

    public void addTransition(MyAllState myAllState) {
        nextStates.put(myAllState.getId(), myAllState);
    }

    public HashMap<String, MyAllState> getNextStates() {
        return nextStates;
    }
}
