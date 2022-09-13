package main.myumlstatemachine;

import main.MyElement;
import com.oocourse.uml2.models.elements.UmlStateMachine;

import java.util.HashMap;

public class MyStateMachine extends MyElement {

    private HashMap<String, MyRegion> regions = new HashMap<>();

    public MyStateMachine(UmlStateMachine umlStateMachine) {
        super(umlStateMachine);
    }

    public void addRegion(MyRegion myRegion) {
        regions.put(myRegion.getId(), myRegion);
    }

    public HashMap<String, MyRegion> getRegions() {
        return regions;
    }
}
