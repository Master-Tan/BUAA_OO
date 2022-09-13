package main;

import com.oocourse.uml3.models.elements.UmlElement;
import com.oocourse.uml3.models.elements.UmlEvent;
import com.oocourse.uml3.models.elements.UmlFinalState;
import com.oocourse.uml3.models.elements.UmlOpaqueBehavior;
import com.oocourse.uml3.models.elements.UmlPseudostate;
import com.oocourse.uml3.models.elements.UmlRegion;
import com.oocourse.uml3.models.elements.UmlState;
import com.oocourse.uml3.models.elements.UmlStateMachine;
import com.oocourse.uml3.models.elements.UmlTransition;
import main.myumlstatemachine.MyAllState;
import main.myumlstatemachine.MyEvent;
import main.myumlstatemachine.MyFinalState;
import main.myumlstatemachine.MyOpaqueBehavior;
import main.myumlstatemachine.MyPseudostate;
import main.myumlstatemachine.MyRegion;
import main.myumlstatemachine.MyState;
import main.myumlstatemachine.MyStateMachine;
import main.myumlstatemachine.MyTransition;

import java.util.ArrayList;
import java.util.HashMap;

public class MyUmlStateMachineParserInit {

    private ArrayList<UmlElement> elements;
    private ArrayList<MyElement> myElements;

    private HashMap<String, MyStateMachine> myStateMachines = new HashMap<>();
    private HashMap<String, MyRegion> myRegions = new HashMap<>();
    private HashMap<String, MyTransition> myTransitions = new HashMap<>();
    private HashMap<String, Integer> stateMachineNames = new HashMap<>();
    private HashMap<String, String> stateMachineNameToId = new HashMap<>();
    private HashMap<String, MyAllState> myAllStates = new HashMap<>();

    public MyUmlStateMachineParserInit(ArrayList<UmlElement> elements,
                                       ArrayList<MyElement> myElements) {

        this.elements = elements;
        this.myElements = myElements;

        /*
            UMLStateMachine:
            设计四个独立的循环
            第一轮处理 UML_STATE_MACHINE
            第二轮处理 UML_REGION
            第三轮处理 UML_STATE、UML_PSEUDOSTATE、UML_FINAL_STATE
            第四轮处理 UML_TRANSITION
            第五轮处理 UML_EVENT、UML_OPAQUE_BEHAVIOR
         */

        this.umlStateMachineInitRound1();
        this.umlStateMachineInitRound2();
        this.umlStateMachineInitRound3();
        this.umlStateMachineInitRound4();
        this.umlStateMachineInitRound5();

    }

    private void umlStateMachineInitRound1() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_STATE_MACHINE: {
                    UmlStateMachine umlStateMachine = (UmlStateMachine) element;
                    MyStateMachine myStateMachine = new MyStateMachine(umlStateMachine);
                    myElements.add(myStateMachine);
                    myStateMachines.put(myStateMachine.getId(), myStateMachine);
                    if (!stateMachineNames.containsKey(myStateMachine.getName())) {
                        stateMachineNames.put(myStateMachine.getName(), 1);
                    } else {
                        stateMachineNames.put(myStateMachine.getName(),
                                stateMachineNames.get(myStateMachine.getName()) + 1);
                    }
                    stateMachineNameToId.put(myStateMachine.getName(), myStateMachine.getId());
                    break;
                }
                default: break;
            }
        }
    }

    private void umlStateMachineInitRound2() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_REGION: {
                    UmlRegion umlRegion = (UmlRegion) element;
                    MyRegion myRegion = new MyRegion(umlRegion);
                    myElements.add(myRegion);
                    MyStateMachine myStateMachine = myStateMachines.get(myRegion.getParentId());
                    myStateMachine.addRegion(myRegion);
                    this.myRegions.put(myRegion.getId(), myRegion);
                    break;
                }
                default: break;
            }
        }
    }

    private void umlStateMachineInitRound3() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_STATE: {
                    UmlState umlState = (UmlState) element;
                    MyState myState = new MyState(umlState);
                    myElements.add(myState);
                    MyRegion myRegion = myRegions.get(myState.getParentId());
                    myRegion.addStates(myState);
                    myAllStates.put(myState.getId(), myState);
                    break;
                }
                case UML_PSEUDOSTATE: {
                    UmlPseudostate umlPseudostate = (UmlPseudostate) element;
                    MyPseudostate myPseudostate = new MyPseudostate(umlPseudostate);
                    myElements.add(myPseudostate);
                    MyRegion myRegion = myRegions.get(myPseudostate.getParentId());
                    myRegion.addPseudoStates(myPseudostate);
                    myAllStates.put(myPseudostate.getId(), myPseudostate);
                    break;
                }
                case UML_FINAL_STATE: {
                    UmlFinalState umlFinalState = (UmlFinalState) element;
                    MyFinalState myFinalState = new MyFinalState(umlFinalState);
                    myElements.add(myFinalState);
                    MyRegion myRegion = myRegions.get(myFinalState.getParentId());
                    myRegion.addFinalStates(myFinalState);
                    myAllStates.put(myFinalState.getId(), myFinalState);
                    break;
                }
                default: break;
            }
        }
    }

    private void umlStateMachineInitRound4() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_TRANSITION: {
                    UmlTransition umlTransition = (UmlTransition) element;
                    MyTransition myTransition = new MyTransition(umlTransition);
                    myElements.add(myTransition);
                    MyRegion myRegion = myRegions.get(myTransition.getParentId());
                    myRegion.addTransitions(myTransition);
                    myTransitions.put(myTransition.getId(), myTransition);
                    String source = myTransition.getSourse();
                    String target = myTransition.getTarget();
                    myAllStates.get(source).addTransition(myTransition, myAllStates.get(target));
                    break;
                }
                default: break;
            }
        }
    }

    private void umlStateMachineInitRound5() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_EVENT: {
                    UmlEvent umlEvent = (UmlEvent) element;
                    MyEvent myEvent = new MyEvent(umlEvent);
                    myElements.add(myEvent);
                    MyTransition myTransition = myTransitions.get(myEvent.getParentId());
                    myTransition.addEvents(myEvent);
                    break;
                }
                case UML_OPAQUE_BEHAVIOR: {
                    UmlOpaqueBehavior umlOpaqueBehavior = (UmlOpaqueBehavior) element;
                    MyOpaqueBehavior myOpaqueBehavior = new MyOpaqueBehavior(umlOpaqueBehavior);
                    myElements.add(myOpaqueBehavior);
                    MyTransition myTransition = myTransitions.get(myOpaqueBehavior.getParentId());
                    myTransition.addOpaqueBehaviors(myOpaqueBehavior);
                    break;
                }
                default: break;
            }
        }
    }

    public ArrayList<UmlElement> getElements() {
        return elements;
    }

    public HashMap<String, MyStateMachine> getMyStateMachines() {
        return myStateMachines;
    }

    public HashMap<String, MyRegion> getMyRegions() {
        return myRegions;
    }

    public HashMap<String, MyTransition> getMyTransitions() {
        return myTransitions;
    }

    public HashMap<String, Integer> getStateMachineNames() {
        return stateMachineNames;
    }

    public HashMap<String, String> getStateMachineNameToId() {
        return stateMachineNameToId;
    }

    public HashMap<String, MyAllState> getMyAllStates() {
        return myAllStates;
    }
}
