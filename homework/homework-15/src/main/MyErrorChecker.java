package main;

import com.oocourse.uml3.interact.common.AttributeClassInformation;
import com.oocourse.uml3.models.common.Direction;
import com.oocourse.uml3.models.common.MessageSort;
import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlClassOrInterface;
import com.oocourse.uml3.models.elements.UmlElement;
import com.oocourse.uml3.models.elements.UmlLifeline;
import main.myumlclass.MyAssociation;
import main.myumlclass.MyAssociationEnd;
import main.myumlclass.MyClass;
import main.myumlclass.MyClassOrInterface;
import main.myumlclass.MyInterface;
import main.myumlclass.MyOperation;
import main.myumlclass.MyParameter;
import main.myumlcollaboration.MyCollaboration;
import main.myumlcollaboration.MyEndPoint;
import main.myumlcollaboration.MyInteraction;
import main.myumlcollaboration.MyLifeline;
import main.myumlcollaboration.MyMessage;
import main.myumlstatemachine.MyAllState;
import main.myumlstatemachine.MyEvent;
import main.myumlstatemachine.MyFinalState;
import main.myumlstatemachine.MyRegion;
import main.myumlstatemachine.MyStateMachine;
import main.myumlstatemachine.MyTransition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class MyErrorChecker {

    private int length;
    private ArrayList<UmlElement> elements;
    private ArrayList<MyElement> myElements;

    private HashMap<String, MyClassOrInterface> myClassOrInterfaces;
    private HashMap<String, UmlClassOrInterface> umlClassOrInterfaces;
    private HashMap<String, MyOperation> myOperations;
    private HashMap<String, Integer> classNames;
    private HashMap<String, String> classNameToId;
    private HashMap<String, MyAssociation> myAssociations;
    private HashMap<String, MyAssociationEnd> myAssociationEnds;

    private HashMap<String, MyStateMachine> myStateMachines;
    private HashMap<String, MyRegion> myRegions;
    private HashMap<String, MyTransition> myTransitions;
    private HashMap<String, Integer> stateMachineNames;
    private HashMap<String, String> stateMachineNameToId;
    private HashMap<String, MyAllState> myAllStates;

    private HashMap<String, MyCollaboration> myCollaborations;
    private HashMap<String, MyInteraction> myInteractions;
    private HashMap<String, Integer> interactionNames;
    private HashMap<String, String> interactionNameToId;
    private HashMap<String, MyLifeline> myLifelines;
    private HashMap<String, UmlLifeline> myUmlLifelines;
    private HashMap<String, MyEndPoint> myEndPoints;

    private MyUmlClassParser myUmlClassParser;
    private MyUmlStateMachineParser myUmlStateMachineParser;
    private MyUmlCollaborationParser myUmlCollaborationParser;

    private HashSet<MyClassOrInterface> olduml003Error;
    private HashSet<MyClassOrInterface> olduml004Error;

    public MyErrorChecker(MyParser myParser) {
        this.length = myParser.getLength();
        this.elements = myParser.getElements();
        this.myElements = myParser.getMyElements();

        this.myClassOrInterfaces = myParser.getMyClassOrInterfaces();
        this.umlClassOrInterfaces = myParser.getUmlClassOrInterfaces();
        this.myOperations = myParser.getMyOperations();
        this.classNames = myParser.getClassNames();
        this.classNameToId = myParser.getClassNameToId();
        this.myAssociations = myParser.getMyAssociations();
        this.myAssociationEnds = myParser.getMyAssociationEnds();

        this.myStateMachines = myParser.getMyStateMachines();
        this.myRegions = myParser.getMyRegions();
        this.myTransitions = myParser.getMyTransitions();
        this.stateMachineNames = myParser.getStateMachineNames();
        this.stateMachineNameToId = myParser.getStateMachineNameToId();
        this.myAllStates = myParser.getMyAllStates();

        this.myCollaborations = myParser.getMyCollaborations();
        this.myInteractions = myParser.getMyInteractions();
        this.interactionNames = myParser.getInteractionNames();
        this.interactionNameToId = myParser.getInteractionNameToId();
        this.myLifelines = myParser.getMyLifelines();
        this.myUmlLifelines = myParser.getMyUmlLifelines();
        this.myEndPoints = myParser.getMyEndPoints();

        this.myUmlClassParser = myParser.getMyUmlClassParser();
        this.myUmlStateMachineParser = myParser.getMyUmlStateMachineParser();
        this.myUmlCollaborationParser = myParser.getMyUmlCollaborationParser();

        this.olduml003Error = myParser.getOldUml003Error();
        this.olduml004Error = myParser.getOlduml004Error();
    }

    public boolean uml001IsOK() {
        for (MyElement myElement : myElements) {
            if ((myElement instanceof MyParameter &&
                    ((MyParameter) myElement).getDirection() != Direction.RETURN) ||
                    myElement instanceof MyClass ||
                    myElement instanceof MyOperation ||
                    myElement instanceof MyInterface) {
                if (MyParser.isEmpty(myElement.getName())) {
                    return false;
                }
            }
            if (myElement instanceof MyAttribute &&
                    myClassOrInterfaces.containsKey(myElement.getParentId())) {
                if (myClassOrInterfaces.get(myElement.getParentId()) instanceof MyClass) {
                    if (MyParser.isEmpty(myElement.getName())) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    private HashSet<AttributeClassInformation> uml002Error = new HashSet<>();

    public boolean uml002IsOK() {
        for (MyClassOrInterface myClassOrInterface : myClassOrInterfaces.values()) {
            if (myClassOrInterface instanceof MyClass) {
                MyClass myClass = ((MyClass) myClassOrInterface);
                HashSet<String> hashSet = new HashSet<>();
                for (MyAttribute myAttribute : myClass.getAttributes().values()) {
                    if (hashSet.contains(myAttribute.getName())) {
                        uml002Error.add(new AttributeClassInformation(
                                myAttribute.getName(), myClass.getName()));
                    } else {
                        hashSet.add(myAttribute.getName());
                    }
                }
                for (MyAssociationEnd myAssociationEnd : myAssociationEnds.values()) {
                    if (myAssociationEnd.getReference().equals(myClass.getId())) {
                        MyAssociation myAssociation =
                                myAssociations.get(myAssociationEnd.getParentId());
                        if (myAssociation.getEnd1().equals(myAssociation.getEnd2())) {
                            continue;
                        }
                        if (myAssociation.getEnd1().equals(myAssociationEnd.getId())) {
                            MyAssociationEnd myAssociationEnd2 =
                                    myAssociationEnds.get(myAssociation.getEnd2());
                            if (hashSet.contains(myAssociationEnd2.getName())) {
                                uml002Error.add(new AttributeClassInformation(
                                        myAssociationEnd2.getName(), myClass.getName()));
                            } else {
                                if (!MyParser.isEmpty(myAssociationEnd2.getName())) {
                                    hashSet.add(myAssociationEnd2.getName());
                                }
                            }
                        } else if (myAssociation.getEnd2().equals(myAssociationEnd.getId())) {
                            MyAssociationEnd myAssociationEnd1 =
                                    myAssociationEnds.get(myAssociation.getEnd1());
                            if (hashSet.contains(myAssociationEnd1.getName())) {
                                uml002Error.add(new AttributeClassInformation(
                                        myAssociationEnd1.getName(), myClass.getName()));
                            } else {
                                if (!MyParser.isEmpty(myAssociationEnd1.getName())) {
                                    hashSet.add(myAssociationEnd1.getName());
                                }
                            }
                        }
                    }
                }
            }
        }
        return uml002Error.isEmpty();
    }

    public HashSet<AttributeClassInformation> getUml002Error() {
        return uml002Error;
    }

    private HashSet<UmlClassOrInterface> uml003Error = new HashSet<>();

    public boolean uml003IsOK() {
        for (MyClassOrInterface myClassOrInterface : myClassOrInterfaces.values()) {
            ArrayList<MyClassOrInterface> queue = new ArrayList<>();
            queue.add(myClassOrInterface);
            int front = 0;
            int end = 0;
            int flag = 0;
            while (front <= end) {
                if (flag == 1) {
                    break;
                }
                MyClassOrInterface classOrInterface = queue.get(front);
                for (MyClassOrInterface element : classOrInterface.getParents().keySet()) {
                    if (classOrInterface.getParents().get(element) == 1 &&
                            element.getId().equals(myClassOrInterface.getId())) {
                        uml003Error.add(umlClassOrInterfaces.get(myClassOrInterface.getId()));
                        flag = 1;
                        break;
                    }
                    if (classOrInterface.getParents().get(element) == 1 &&
                            !queue.contains(element)) {
                        queue.add(element);
                        end++;
                    }
                }
                front++;
            }
        }
        // 自环特例
        for (MyClassOrInterface myClassOrInterface : olduml003Error) {
            this.uml003Error.add(umlClassOrInterfaces.get(myClassOrInterface.getId()));
        }
        return uml003Error.isEmpty();
    }

    HashSet<UmlClassOrInterface> getUml003Error() {
        return uml003Error;
    }

    private HashSet<UmlClassOrInterface> uml004Error = new HashSet<>();

    public boolean uml004IsOK() {
        for (MyClassOrInterface myClassOrInterface : olduml004Error) {
            for (MyClassOrInterface classOrInterface : myClassOrInterface.getChildren().keySet()) {
                this.uml004Error.add(umlClassOrInterfaces.get(classOrInterface.getId()));
            }
        }
        return this.uml004Error.isEmpty();
    }

    public HashSet<UmlClassOrInterface> getUml004Error() {
        return uml004Error;
    }

    public boolean uml005IsOK() {
        for (MyClassOrInterface myClassOrInterface : myClassOrInterfaces.values()) {
            if (myClassOrInterface instanceof MyInterface) {
                for (MyAttribute myAttribute : myClassOrInterface.getAttributes().values()) {
                    if (myAttribute.getVisibility() != Visibility.PUBLIC) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    public boolean uml006IsOK() {
        for (MyLifeline myLifeline : myLifelines.values()) {
            MyInteraction myInteraction = myInteractions.get(myLifeline.getParentId());
            MyCollaboration myCollaboration = myCollaborations.get(myInteraction.getParentId());
            if (!myCollaboration.getAttributes().containsKey(myLifeline.getRepresent())) {
                return false;
            }
        }
        return true;
    }

    public boolean uml007IsOK() {
        for (MyLifeline myLifeline : myLifelines.values()) {
            ArrayList<MyMessage> myMessages = myLifeline.getReceiveMessages();
            int flag;
            flag = 0;
            for (MyMessage myMessage : myMessages) {
                if (flag == 1) {
                    return false;
                }
                if (myMessage.getMessageSort() == MessageSort.DELETE_MESSAGE) {
                    flag = 1;
                }
            }
        }
        return true;
    }

    public boolean uml008IsOK() {
        for (MyAllState myAllState : myAllStates.values()) {
            if (myAllState instanceof MyFinalState) {
                if (myAllState.getNextStates().size() != 0) {
                    return false;
                }
            }
        }
        return true;
    }

    public boolean uml009IsOK() {
        for (MyAllState myAllState : myAllStates.values()) {
            ArrayList<MyEvent> events = new ArrayList<>();
            for (MyTransition myTransition : myAllState.getOutTransition().values()) {
                for (MyEvent myEvent : myTransition.getEvents().values()) {
                    for (MyEvent event : events) {
                        if (event.getName() == null) {
                            if (myEvent.getName() == null) {
                                if (MyParser.isEmpty(
                                        myTransitions.get(event.getParentId()).getGuard())) {
                                    return false;
                                }
                                if (MyParser.isEmpty(
                                        myTransitions.get(myEvent.getParentId()).getGuard())) {
                                    return false;
                                }
                                if (myTransitions.get(event.getParentId()).getGuard().equals(
                                        myTransitions.get(myEvent.getParentId()).getGuard())) {
                                    return false;
                                }
                            }
                        } else {
                            if (event.getName().equals(myEvent.getName())) {
                                if (MyParser.isEmpty(
                                        myTransitions.get(event.getParentId()).getGuard())) {
                                    return false;
                                }
                                if (MyParser.isEmpty(
                                        myTransitions.get(myEvent.getParentId()).getGuard())) {
                                    return false;
                                }
                                if (myTransitions.get(event.getParentId()).getGuard().equals(
                                        myTransitions.get(myEvent.getParentId()).getGuard())) {
                                    return false;
                                }
                            }
                        }
                    }
                    events.add(myEvent);
                }
            }
        }
        return true;
    }

}
