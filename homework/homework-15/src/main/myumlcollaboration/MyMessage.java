package main.myumlcollaboration;

import main.MyElement;
import com.oocourse.uml3.models.common.MessageSort;
import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlMessage;

public class MyMessage extends MyElement {

    private MessageSort messageSort;
    private Visibility visibility;
    private String sourse;
    private String target;

    public MyMessage(UmlMessage umlMessage) {
        super(umlMessage);

        this.messageSort = umlMessage.getMessageSort();
        this.visibility = umlMessage.getVisibility();
        this.sourse = umlMessage.getSource();
        this.target = umlMessage.getTarget();
    }

    public MessageSort getMessageSort() {
        return messageSort;
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public String getSourse() {
        return sourse;
    }

    public String getTarget() {
        return target;
    }
}
