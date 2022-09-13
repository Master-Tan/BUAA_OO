package main;

import main.myumlclass.MyClassOrInterface;
import main.myumlclass.MyOperation;
import main.myumlcollaboration.MyCollaboration;
import main.myumlcollaboration.MyEndPoint;
import main.myumlcollaboration.MyInteraction;
import main.myumlcollaboration.MyLifeline;
import main.myumlstatemachine.MyAllState;
import main.myumlstatemachine.MyRegion;
import main.myumlstatemachine.MyStateMachine;
import main.myumlstatemachine.MyTransition;
import com.oocourse.uml2.interact.common.Pair;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlLifeline;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class MyParser {

    private int length;
    private ArrayList<UmlElement> elements = new ArrayList<>();
    private HashMap<String, MyClassOrInterface> myClassOrInterfaces;
    private HashMap<String, MyOperation> myOperations;
    private HashMap<String, Integer> classNames;
    private HashMap<String, String> classNameToId;

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

    public MyParser(UmlElement... elements) {

        this.length = elements.length;

        for (int i = 0; i < length; i++) {
            this.elements.add(elements[i]);
            //              System.out.println("\n" + elements[i].getElementType());
            //              System.out.println(elements[i].toJson());
            //              System.out.println(elements[i].getClass().getSimpleName());
        }

        MyUmlClassParserInit myUmlClassParserInit;
        myUmlClassParserInit = new MyUmlClassParserInit(this.elements);
        MyUmlStateMachineParserInit myUmlStateMachineParserInit;
        myUmlStateMachineParserInit = new MyUmlStateMachineParserInit(this.elements);
        MyUmlCollaborationParserInit myUmlCollaborationParserInit;
        myUmlCollaborationParserInit = new MyUmlCollaborationParserInit(this.elements);

        this.myClassOrInterfaces = myUmlClassParserInit.getMyClassOrInterfaces();
        this.myOperations = myUmlClassParserInit.getMyOperations();
        this.classNames = myUmlClassParserInit.getClassNames();
        this.classNameToId = myUmlClassParserInit.getClassNameToId();

        this.myStateMachines = myUmlStateMachineParserInit.getMyStateMachines();
        this.myRegions = myUmlStateMachineParserInit.getMyRegions();
        this.myTransitions = myUmlStateMachineParserInit.getMyTransitions();
        this.stateMachineNames = myUmlStateMachineParserInit.getStateMachineNames();
        this.stateMachineNameToId = myUmlStateMachineParserInit.getStateMachineNameToId();
        this.myAllStates = myUmlStateMachineParserInit.getMyAllStates();

        this.myCollaborations = myUmlCollaborationParserInit.getMyCollaborations();
        this.myInteractions = myUmlCollaborationParserInit.getMyInteractions();
        this.interactionNames = myUmlCollaborationParserInit.getInteractionNames();
        this.interactionNameToId = myUmlCollaborationParserInit.getInteractionNameToId();
        this.myLifelines = myUmlCollaborationParserInit.getMyLifelines();
        this.myUmlLifelines = myUmlCollaborationParserInit.getMyUmlLifelines();
        this.myEndPoints = myUmlCollaborationParserInit.getMyEndPoints();

        myUmlClassParser = new MyUmlClassParser(myClassOrInterfaces,
                myOperations, classNames, classNameToId);

        myUmlStateMachineParser = new MyUmlStateMachineParser(myStateMachines,
                myRegions, myTransitions, stateMachineNames, stateMachineNameToId,
                myAllStates);

        myUmlCollaborationParser = new MyUmlCollaborationParser(myCollaborations,
                myInteractions, interactionNames, interactionNameToId, myLifelines,
                myUmlLifelines, myEndPoints);

    }

    public int getClassCount() {
        return myUmlClassParser.getClassCount();
    }

    public boolean isClassExist(String className) {
        return myUmlClassParser.isClassExist(className);
    }

    public boolean isClassRepeat(String className) {
        return myUmlClassParser.isClassRepeat(className);
    }

    public int getClassSubclassCount(String className) {
        return myUmlClassParser.getClassSubclassCount(className);
    }

    public int getOperationCount(String className) {
        return myUmlClassParser.getOperationCount(className);
    }

    public Map<Visibility, Integer> getClassOperationVisibility(
            String className, String methodName) {
        return myUmlClassParser.getClassOperationVisibility(className, methodName);
    }

    public boolean isOperationWrongType(String className, String methodName) {
        return myUmlClassParser.isOperationWrongType(className, methodName);
    }

    public boolean isOperationRepeat(String className, String methodName) {
        return myUmlClassParser.isOperationRepeat(className, methodName);
    }

    public List<Integer> getClassOperationCouplingDegree(
            String className, String methodName) {
        return myUmlClassParser.getClassOperationCouplingDegree(className, methodName);
    }

    public int getClassAttributeCouplingDegree(String className) {
        return myUmlClassParser.getClassAttributeCouplingDegree(className);
    }

    public List<String> getClassImplementInterfaceList(String className) {
        return myUmlClassParser.getClassImplementInterfaceList(className);
    }

    public int getClassDepthOfInheritance(String className) {
        return myUmlClassParser.getClassDepthOfInheritance(className);
    }

    public boolean isInteractionExist(String interactionName) {
        return interactionNames.containsKey(interactionName);
    }

    public boolean isInteractionRepeat(String className) {
        if (interactionNames.containsKey(className)) {
            if (interactionNames.get(className) > 1) {
                return true;
            }
        }
        return false;
    }

    public int getParticipantCount(String interactionName) {
        return myUmlCollaborationParser.getParticipantCount(interactionName);
    }

    public boolean isLifelineExist(String interactionName, String lifelineName) {
        return myUmlCollaborationParser.isLifelineExist(interactionName, lifelineName);
    }

    public boolean isLifelineRepeat(String interactionName, String lifelineName) {
        return myUmlCollaborationParser.isLifelineRepeat(interactionName, lifelineName);
    }

    public boolean isLifelineCreateExist(String interactionName, String lifelineName) {
        return myUmlCollaborationParser.isLifelineCreateExist(interactionName, lifelineName);
    }

    public boolean isLifelineCreateRepeat(String interactionName, String lifelineName) {
        return myUmlCollaborationParser.isLifelineCreateRepeat(interactionName, lifelineName);
    }

    public UmlLifeline getParticipantCreator(String interactionName, String lifelineName) {
        return myUmlCollaborationParser.getParticipantCreator(interactionName, lifelineName);
    }

    public Pair<Integer, Integer> getParticipantLostAndFound(String interactionName,
                                                             String lifelineName) {

        return myUmlCollaborationParser.getParticipantLostAndFound(interactionName, lifelineName);
    }

    public boolean isStateMachineExist(String stateMachineName) {
        return myUmlStateMachineParser.isStateMachineExist(stateMachineName);
    }

    public boolean isStateMachineRepeat(String stateMachineName) {
        return myUmlStateMachineParser.isStateMachineRepeat(stateMachineName);
    }

    public int getStateCount(String stateMachineName) {
        return myUmlStateMachineParser.getStateCount(stateMachineName);
    }

    public boolean isStateExist(String stateMachineName, String stateName) {
        return myUmlStateMachineParser.isStateExist(stateMachineName, stateName);
    }

    public boolean isStateRepeat(String stateMachineName, String stateName) {
        return myUmlStateMachineParser.isStateRepeat(stateMachineName, stateName);
    }

    public boolean getStateIsCriticalPoint(String stateMachineName, String stateName) {
        return myUmlStateMachineParser.getStateIsCriticalPoint(stateMachineName, stateName);
    }

    public boolean isTransitionExist(String stateMachineName,
                                     String sourceStateName, String targetStateName) {
        return myUmlStateMachineParser.isTransitionExist(stateMachineName,
                sourceStateName, targetStateName);
    }

    public List<String> getTransitionTrigger(String stateMachineName,
                                             String sourceStateName, String targetStateName) {
        return myUmlStateMachineParser.getTransitionTrigger(stateMachineName,
                sourceStateName, targetStateName);
    }

}
