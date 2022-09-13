package main.myumlstatemachine;

import main.MyElement;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlTransition;

import java.util.HashMap;

public class MyTransition extends MyElement {

    private Visibility visibility;
    private String guard;
    private String sourse;
    private String target;

    private HashMap<String, MyEvent> events = new HashMap<>();
    private HashMap<String, MyOpaqueBehavior> opaqueBehaviors = new HashMap<>();

    public MyTransition(UmlTransition umlTransition) {
        super(umlTransition);

        this.visibility = umlTransition.getVisibility();
        this.guard = umlTransition.getGuard();
        this.sourse = umlTransition.getSource();
        this.target = umlTransition.getTarget();

    }

    public void addEvents(MyEvent myEvent) {
        events.put(myEvent.getId(), myEvent);
    }

    public void addOpaqueBehaviors(MyOpaqueBehavior myOpaqueBehavior) {
        opaqueBehaviors.put(myOpaqueBehavior.getId(), myOpaqueBehavior);
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public String getGuard() {
        return guard;
    }

    public String getSourse() {
        return sourse;
    }

    public String getTarget() {
        return target;
    }

    public HashMap<String, MyEvent> getEvents() {
        return events;
    }

    public HashMap<String, MyOpaqueBehavior> getOpaqueBehaviors() {
        return opaqueBehaviors;
    }
}
