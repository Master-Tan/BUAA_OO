package main.myumlcollaboration;

import main.MyElement;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlEndpoint;

import java.util.ArrayList;

public class MyEndPoint extends MyElement {

    private Visibility visibility;

    private ArrayList<String> senders = new ArrayList<>();
    private ArrayList<MyMessage> sendMessages = new ArrayList<>();
    private ArrayList<String> receivers = new ArrayList<>();
    private ArrayList<MyMessage> receiveMessages = new ArrayList<>();

    public MyEndPoint(UmlEndpoint umlEndpoint) {
        super(umlEndpoint);

        this.visibility = umlEndpoint.getVisibility();
    }

    public void sendMessage(String target, MyMessage myMessage) {
        senders.add(target);
        sendMessages.add(myMessage);
    }

    public void receiveMessage(String source, MyMessage myMessage) {
        receivers.add(source);
        receiveMessages.add(myMessage);
    }

    public ArrayList<String> getSenders() {
        return senders;
    }

    public ArrayList<MyMessage> getSendMessages() {
        return sendMessages;
    }

    public ArrayList<String> getReceivers() {
        return receivers;
    }

    public ArrayList<MyMessage> getReceiveMessages() {
        return receiveMessages;
    }
}
