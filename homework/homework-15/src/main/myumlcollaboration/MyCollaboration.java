package main.myumlcollaboration;

import main.MyAttribute;
import main.MyElement;
import com.oocourse.uml3.models.elements.UmlCollaboration;

import java.util.HashMap;

public class MyCollaboration extends MyElement {

    private HashMap<String, MyInteraction> interactions = new HashMap<>();
    private HashMap<String, MyAttribute> attributes = new HashMap<>();

    public MyCollaboration(UmlCollaboration umlCollaboration) {
        super(umlCollaboration);
    }

    public void addInteraction(MyInteraction myInteraction) {
        interactions.put(myInteraction.getId(), myInteraction);
    }

    public void addAttribute(MyAttribute myAttribute) {
        attributes.put(myAttribute.getId(), myAttribute);
    }

    public HashMap<String, MyInteraction> getInteractions() {
        return interactions;
    }

    public HashMap<String, MyAttribute> getAttributes() {
        return attributes;
    }
}
