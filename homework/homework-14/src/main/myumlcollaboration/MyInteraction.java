package main.myumlcollaboration;

import main.MyElement;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlInteraction;

import java.util.HashMap;

public class MyInteraction extends MyElement {

    private Visibility visibility;

    private HashMap<String, MyMessage> messages = new HashMap<>();
    private HashMap<String, MyLifeline> lifelines = new HashMap<>();
    private HashMap<String, MyEndPoint> endPoints = new HashMap<>();

    public MyInteraction(UmlInteraction umlInteraction) {
        super(umlInteraction);

        this.visibility = umlInteraction.getVisibility();
    }

    public void addMessage(MyMessage myMessage) {
        messages.put(myMessage.getId(), myMessage);
    }

    public void addLifeline(MyLifeline myLifeline) {
        lifelines.put(myLifeline.getId(), myLifeline);
    }

    public void addEndPoint(MyEndPoint myEndPoint) {
        endPoints.put(myEndPoint.getId(), myEndPoint);
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public HashMap<String, MyMessage> getMessages() {
        return messages;
    }

    public HashMap<String, MyLifeline> getLifelines() {
        return lifelines;
    }

    public HashMap<String, MyEndPoint> getEndPoints() {
        return endPoints;
    }
}
