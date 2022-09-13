package main.myumlcollaboration;

import main.MyElement;
import com.oocourse.uml2.models.elements.UmlLifeline;

import java.util.ArrayList;

public class MyLifeline extends MyElement {

    private String represent;
    private boolean isMultiInstance;

    private ArrayList<String> senders = new ArrayList<>();
    private ArrayList<MyMessage> sendMessages = new ArrayList<>();
    private ArrayList<String> receivers = new ArrayList<>();
    private ArrayList<MyMessage> receiveMessages = new ArrayList<>();

    public MyLifeline(UmlLifeline umlLifeline) {
        super(umlLifeline);

        this.represent = umlLifeline.getRepresent();
        this.isMultiInstance = umlLifeline.isMultiInstance();
    }

    public void sendMessage(String target, MyMessage myMessage) {
        senders.add(target);
        sendMessages.add(myMessage);
    }

    public void receiveMessage(String source, MyMessage myMessage) {
        receivers.add(source);
        receiveMessages.add(myMessage);
    }

    public String getRepresent() {
        return represent;
    }

    public boolean isMultiInstance() {
        return isMultiInstance;
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
