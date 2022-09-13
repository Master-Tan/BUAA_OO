package main;

import com.oocourse.uml3.interact.common.AttributeClassInformation;
import com.oocourse.uml3.models.elements.UmlClassOrInterface;
import main.myumlclass.MyAssociation;
import main.myumlclass.MyAssociationEnd;
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
import com.oocourse.uml3.interact.common.Pair;
import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlElement;
import com.oocourse.uml3.models.elements.UmlLifeline;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MyParser {

    private int length;
    private ArrayList<UmlElement> elements = new ArrayList<>();
    private ArrayList<MyElement> myElements = new ArrayList<>();

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

    private HashSet<MyClassOrInterface> uml003Error;
    private HashSet<MyClassOrInterface> uml004Error;

    private MyErrorChecker myErrorChecker;

    public MyParser(UmlElement... elements) {

        this.length = elements.length;

        for (int i = 0; i < length; i++) {
            this.elements.add(elements[i]);
            //              System.out.println("\n" + elements[i].getElementType());
            //              System.out.println(elements[i].toJson());
            //              System.out.println(elements[i].getClass().getSimpleName());
        }

        this.uml003Error = new HashSet<>();
        this.uml004Error = new HashSet<>();

        MyUmlClassParserInit myUmlClassParserInit;
        myUmlClassParserInit = new MyUmlClassParserInit(this.elements, myElements,
                uml003Error, uml004Error);
        MyUmlStateMachineParserInit myUmlStateMachineParserInit;
        myUmlStateMachineParserInit = new MyUmlStateMachineParserInit(this.elements, myElements);
        MyUmlCollaborationParserInit myUmlCollaborationParserInit;
        myUmlCollaborationParserInit = new MyUmlCollaborationParserInit(this.elements, myElements);

        this.myClassOrInterfaces = myUmlClassParserInit.getMyClassOrInterfaces();
        this.umlClassOrInterfaces = myUmlClassParserInit.getUmlClassOrInterface();
        this.myOperations = myUmlClassParserInit.getMyOperations();
        this.classNames = myUmlClassParserInit.getClassNames();
        this.classNameToId = myUmlClassParserInit.getClassNameToId();
        this.myAssociations = myUmlClassParserInit.getMyAssociations();
        this.myAssociationEnds = myUmlClassParserInit.getMyAssociationEnds();

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

        myUmlClassParser = new MyUmlClassParser(myClassOrInterfaces, umlClassOrInterfaces,
                myOperations, classNames, classNameToId, myAssociations, myAssociationEnds);

        myUmlStateMachineParser = new MyUmlStateMachineParser(myStateMachines,
                myRegions, myTransitions, stateMachineNames, stateMachineNameToId,
                myAllStates);

        myUmlCollaborationParser = new MyUmlCollaborationParser(myCollaborations,
                myInteractions, interactionNames, interactionNameToId, myLifelines,
                myUmlLifelines, myEndPoints);

        myErrorChecker = new MyErrorChecker(this);
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
        return myUmlCollaborationParser.isInteractionExist(interactionName);
    }

    public boolean isInteractionRepeat(String interactionName) {
        return myUmlCollaborationParser.isInteractionRepeat(interactionName);
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

    public boolean uml001IsOK() {
        return myErrorChecker.uml001IsOK();
    }

    public boolean uml002IsOK() {
        return myErrorChecker.uml002IsOK();
    }

    public HashSet<AttributeClassInformation> getUml002Error() {
        return myErrorChecker.getUml002Error();
    }

    public boolean uml003IsOK() {
        return myErrorChecker.uml003IsOK();
    }

    HashSet<UmlClassOrInterface> getUml003Error() {
        return myErrorChecker.getUml003Error();
    }

    public boolean uml004IsOK() {
        return myErrorChecker.uml004IsOK();
    }

    public HashSet<UmlClassOrInterface> getUml004Error() {
        return myErrorChecker.getUml004Error();
    }

    public boolean uml005IsOK() {
        return myErrorChecker.uml005IsOK();
    }

    public boolean uml006IsOK() {
        return myErrorChecker.uml006IsOK();
    }

    public boolean uml007IsOK() {
        return myErrorChecker.uml007IsOK();
    }

    public boolean uml008IsOK() {
        return myErrorChecker.uml008IsOK();
    }

    public boolean uml009IsOK() {
        return myErrorChecker.uml009IsOK();
    }

    public int getLength() {
        return length;
    }

    public ArrayList<UmlElement> getElements() {
        return elements;
    }

    public ArrayList<MyElement> getMyElements() {
        return myElements;
    }

    public HashMap<String, MyClassOrInterface> getMyClassOrInterfaces() {
        return myClassOrInterfaces;
    }

    public HashMap<String, UmlClassOrInterface> getUmlClassOrInterfaces() {
        return umlClassOrInterfaces;
    }

    public HashMap<String, MyOperation> getMyOperations() {
        return myOperations;
    }

    public HashMap<String, Integer> getClassNames() {
        return classNames;
    }

    public HashMap<String, String> getClassNameToId() {
        return classNameToId;
    }

    public HashMap<String, MyAssociation> getMyAssociations() {
        return myAssociations;
    }

    public HashMap<String, MyAssociationEnd> getMyAssociationEnds() {
        return myAssociationEnds;
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

    public MyUmlClassParser getMyUmlClassParser() {
        return myUmlClassParser;
    }

    public MyUmlStateMachineParser getMyUmlStateMachineParser() {
        return myUmlStateMachineParser;
    }

    public MyUmlCollaborationParser getMyUmlCollaborationParser() {
        return myUmlCollaborationParser;
    }

    public HashSet<MyClassOrInterface> getOldUml003Error() {
        return uml003Error;
    }

    public HashSet<MyClassOrInterface> getOlduml004Error() {
        return uml004Error;
    }

    public static boolean isEmpty(String string) {
        Pattern pattern = Pattern.compile("^[ \t]*$");
        if (string == null) {
            return true;
        } else {
            Matcher matcher = pattern.matcher(string);
            if (matcher.find()) {
                return true;
            }
        }
        return false;
    }

}
