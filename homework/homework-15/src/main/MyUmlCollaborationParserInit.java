package main;

import com.oocourse.uml3.models.elements.UmlAttribute;
import com.oocourse.uml3.models.elements.UmlCollaboration;
import com.oocourse.uml3.models.elements.UmlElement;
import com.oocourse.uml3.models.elements.UmlEndpoint;
import com.oocourse.uml3.models.elements.UmlInteraction;
import com.oocourse.uml3.models.elements.UmlLifeline;
import com.oocourse.uml3.models.elements.UmlMessage;
import main.myumlcollaboration.MyCollaboration;
import main.myumlcollaboration.MyEndPoint;
import main.myumlcollaboration.MyInteraction;
import main.myumlcollaboration.MyLifeline;
import main.myumlcollaboration.MyMessage;

import java.util.ArrayList;
import java.util.HashMap;

public class MyUmlCollaborationParserInit {

    private ArrayList<UmlElement> elements;
    private ArrayList<MyElement> myElements;

    private HashMap<String, MyCollaboration> myCollaborations = new HashMap<>();
    private HashMap<String, MyInteraction> myInteractions = new HashMap<>();
    private HashMap<String, Integer> interactionNames = new HashMap<>();
    private HashMap<String, String> interactionNameToId = new HashMap<>();
    private HashMap<String, MyLifeline> myLifelines = new HashMap<>();
    private HashMap<String, UmlLifeline> myUmlLifelines = new HashMap<>();
    private HashMap<String, MyEndPoint> myEndPoints = new HashMap<>();

    public MyUmlCollaborationParserInit(ArrayList<UmlElement> elements,
                                        ArrayList<MyElement> myElements) {

        this.elements = elements;
        this.myElements = myElements;

        /*
            UMLCollaboration:
            设计四个独立的循环
            第一轮处理 UML_COLLABORATION
            第二轮处理 UML_INTERACTION、UML_ATTRIBUTE
            第三轮处理 UML_LIFELINE、UML_ENDPOINT
            第四轮处理 UML_MESSAGE
         */

        this.umlCollaborationInitRound1();
        this.umlCollaborationInitRound2();
        this.umlCollaborationInitRound3();
        this.umlCollaborationInitRound4();

    }

    private void umlCollaborationInitRound1() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_COLLABORATION: {
                    UmlCollaboration umlCollaboration = (UmlCollaboration) element;
                    MyCollaboration myCollaboration = new MyCollaboration(umlCollaboration);
                    myElements.add(myCollaboration);
                    myCollaborations.put(myCollaboration.getId(), myCollaboration);
                    break;
                }
                default: break;
            }
        }
    }

    private void umlCollaborationInitRound2() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_INTERACTION: {
                    UmlInteraction umlInteraction = (UmlInteraction) element;
                    MyInteraction myInteraction = new MyInteraction(umlInteraction);
                    myElements.add(myInteraction);
                    MyCollaboration myCollaboration =
                            myCollaborations.get(myInteraction.getParentId());
                    myCollaboration.addInteraction(myInteraction);
                    myInteractions.put(myInteraction.getId(), myInteraction);
                    if (!interactionNames.containsKey(myInteraction.getName())) {
                        interactionNames.put(myInteraction.getName(), 1);
                    } else {
                        interactionNames.put(myInteraction.getName(),
                                interactionNames.get(myInteraction.getName()) + 1);
                    }
                    interactionNameToId.put(myInteraction.getName(), myInteraction.getId());
                    break;
                }
                case UML_ATTRIBUTE: {
                    UmlAttribute umlAttribute = (UmlAttribute) element;
                    MyAttribute myAttribute = new MyAttribute(umlAttribute);
                    myElements.add(myAttribute);
                    if (myCollaborations.containsKey(myAttribute.getParentId())) {
                        MyCollaboration myCollaboration =
                                myCollaborations.get(myAttribute.getParentId());
                        myCollaboration.addAttribute(myAttribute);
                    }
                    break;
                }
                default: break;
            }
        }
    }

    private void umlCollaborationInitRound3() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_LIFELINE: {
                    UmlLifeline umlLifeline = (UmlLifeline) element;
                    MyLifeline myLifeline = new MyLifeline(umlLifeline);
                    myElements.add(myLifeline);
                    MyInteraction myInteraction = myInteractions.get(myLifeline.getParentId());
                    myInteraction.addLifeline(myLifeline);
                    myUmlLifelines.put(myLifeline.getId(), umlLifeline);
                    myLifelines.put(myLifeline.getId(), myLifeline);
                    break;
                }
                case UML_ENDPOINT: {
                    UmlEndpoint umlEndpoint = (UmlEndpoint) element;
                    MyEndPoint myEndPoint = new MyEndPoint(umlEndpoint);
                    myElements.add(myEndPoint);
                    MyInteraction myInteraction = myInteractions.get(myEndPoint.getParentId());
                    myInteraction.addEndPoint(myEndPoint);
                    myEndPoints.put(myEndPoint.getId(), myEndPoint);
                    break;
                }
                default: break;
            }
        }
    }

    private void umlCollaborationInitRound4() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_MESSAGE: {
                    UmlMessage umlMessage = (UmlMessage) element;
                    MyMessage myMessage = new MyMessage(umlMessage);
                    myElements.add(myMessage);
                    MyInteraction myInteraction = myInteractions.get(myMessage.getParentId());
                    myInteraction.addMessage(myMessage);
                    String source = myMessage.getSourse();
                    String target = myMessage.getTarget();
                    if (myEndPoints.containsKey(source)) {
                        myEndPoints.get(source).sendMessage(target, myMessage);
                    } else if (myLifelines.containsKey(source)) {
                        myLifelines.get(source).sendMessage(target, myMessage);
                    }
                    if (myEndPoints.containsKey(target)) {
                        myEndPoints.get(target).receiveMessage(source, myMessage);
                    } else if (myLifelines.containsKey(target)) {
                        myLifelines.get(target).receiveMessage(source, myMessage);
                    }
                    break;
                }
                default: break;
            }
        }
    }

    public ArrayList<UmlElement> getElements() {
        return elements;
    }

    public HashMap<String, MyCollaboration> getMyCollaborations() {
        return myCollaborations;
    }

    public HashMap<String, MyInteraction> getMyInteractions() {
        return myInteractions;
    }

    public HashMap<String, Integer> getInteractionNames() {
        return interactionNames;
    }

    public HashMap<String, String> getInteractionNameToId() {
        return interactionNameToId;
    }

    public HashMap<String, MyLifeline> getMyLifelines() {
        return myLifelines;
    }

    public HashMap<String, UmlLifeline> getMyUmlLifelines() {
        return myUmlLifelines;
    }

    public HashMap<String, MyEndPoint> getMyEndPoints() {
        return myEndPoints;
    }
}
