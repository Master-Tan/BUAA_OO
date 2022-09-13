package main;

import com.oocourse.uml3.interact.common.AttributeClassInformation;
import com.oocourse.uml3.interact.common.Pair;
import com.oocourse.uml3.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml3.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml3.interact.exceptions.user.InteractionDuplicatedException;
import com.oocourse.uml3.interact.exceptions.user.InteractionNotFoundException;
import com.oocourse.uml3.interact.exceptions.user.LifelineCreatedRepeatedlyException;
import com.oocourse.uml3.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml3.interact.exceptions.user.LifelineNeverCreatedException;
import com.oocourse.uml3.interact.exceptions.user.LifelineNotFoundException;
import com.oocourse.uml3.interact.exceptions.user.MethodDuplicatedException;
import com.oocourse.uml3.interact.exceptions.user.MethodWrongTypeException;
import com.oocourse.uml3.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml3.interact.exceptions.user.StateMachineDuplicatedException;
import com.oocourse.uml3.interact.exceptions.user.StateMachineNotFoundException;
import com.oocourse.uml3.interact.exceptions.user.StateNotFoundException;
import com.oocourse.uml3.interact.exceptions.user.TransitionNotFoundException;
import com.oocourse.uml3.interact.exceptions.user.UmlRule001Exception;
import com.oocourse.uml3.interact.exceptions.user.UmlRule002Exception;
import com.oocourse.uml3.interact.exceptions.user.UmlRule003Exception;
import com.oocourse.uml3.interact.exceptions.user.UmlRule004Exception;
import com.oocourse.uml3.interact.exceptions.user.UmlRule005Exception;
import com.oocourse.uml3.interact.exceptions.user.UmlRule006Exception;
import com.oocourse.uml3.interact.exceptions.user.UmlRule007Exception;
import com.oocourse.uml3.interact.exceptions.user.UmlRule008Exception;
import com.oocourse.uml3.interact.exceptions.user.UmlRule009Exception;
import com.oocourse.uml3.interact.format.UserApi;
import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlClassOrInterface;
import com.oocourse.uml3.models.elements.UmlElement;
import com.oocourse.uml3.models.elements.UmlLifeline;

import java.util.HashSet;
import java.util.List;
import java.util.Map;

public class MyImplementation implements UserApi {

    private MyParser myParser;

    public MyImplementation(UmlElement... elements) {
        myParser = new MyParser(elements);
    }

    // 第一次作业
    @Override
    public int getClassCount() {
        int classCount;
        classCount = myParser.getClassCount();
        return classCount;
    }

    @Override
    public int getClassSubClassCount(String className) throws
            ClassNotFoundException, ClassDuplicatedException {
        if (!myParser.isClassExist(className)) {
            throw new ClassNotFoundException(className);
        }
        if (myParser.isClassRepeat(className)) {
            throw new ClassDuplicatedException(className);
        }
        int classSubClassCount;
        classSubClassCount = myParser.getClassSubclassCount(className);
        return classSubClassCount;
    }

    @Override
    public int getClassOperationCount(String className) throws
            ClassNotFoundException, ClassDuplicatedException {
        if (!myParser.isClassExist(className)) {
            throw new ClassNotFoundException(className);
        }
        if (myParser.isClassRepeat(className)) {
            throw new ClassDuplicatedException(className);
        }
        int classOperationCount;
        classOperationCount = myParser.getOperationCount(className);
        return classOperationCount;
    }

    @Override
    public Map<Visibility, Integer> getClassOperationVisibility(String className,
                                                                String methodName)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!myParser.isClassExist(className)) {
            throw new ClassNotFoundException(className);
        }
        if (myParser.isClassRepeat(className)) {
            throw new ClassDuplicatedException(className);
        }
        Map<Visibility, Integer> classOperationVisibility;
        classOperationVisibility = myParser.getClassOperationVisibility(className, methodName);
        return classOperationVisibility;
    }

    @Override
    public List<Integer> getClassOperationCouplingDegree(String className,
                                                         String methodName)
            throws ClassNotFoundException, ClassDuplicatedException,
            MethodWrongTypeException, MethodDuplicatedException {
        if (!myParser.isClassExist(className)) {
            throw new ClassNotFoundException(className);
        }
        if (myParser.isClassRepeat(className)) {
            throw new ClassDuplicatedException(className);
        }
        if (myParser.isOperationWrongType(className, methodName)) {
            throw new MethodWrongTypeException(className, methodName);
        }
        if (myParser.isOperationRepeat(className, methodName)) {
            throw new MethodDuplicatedException(className, methodName);
        }
        List<Integer> classOperationCouplingDegree;
        classOperationCouplingDegree = myParser.getClassOperationCouplingDegree(
                className, methodName);
        return classOperationCouplingDegree;
    }

    @Override
    public int getClassAttributeCouplingDegree(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!myParser.isClassExist(className)) {
            throw new ClassNotFoundException(className);
        }
        if (myParser.isClassRepeat(className)) {
            throw new ClassDuplicatedException(className);
        }
        int classAttributeCouplingDegree;
        classAttributeCouplingDegree = myParser.getClassAttributeCouplingDegree(className);
        return classAttributeCouplingDegree;
    }

    @Override
    public List<String> getClassImplementInterfaceList(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!myParser.isClassExist(className)) {
            throw new ClassNotFoundException(className);
        }
        if (myParser.isClassRepeat(className)) {
            throw new ClassDuplicatedException(className);
        }
        List<String> classImplementInterfaceList;
        classImplementInterfaceList = myParser.getClassImplementInterfaceList(className);
        return classImplementInterfaceList;
    }

    @Override
    public int getClassDepthOfInheritance(String className)
            throws ClassNotFoundException, ClassDuplicatedException {
        if (!myParser.isClassExist(className)) {
            throw new ClassNotFoundException(className);
        }
        if (myParser.isClassRepeat(className)) {
            throw new ClassDuplicatedException(className);
        }
        int classDepthOfInheritance;
        classDepthOfInheritance = myParser.getClassDepthOfInheritance(className);
        return classDepthOfInheritance;
    }

    // 第二次作业
    @Override
    public int getParticipantCount(String interactionName)
            throws InteractionNotFoundException, InteractionDuplicatedException {
        if (!myParser.isInteractionExist(interactionName)) {
            throw new InteractionNotFoundException(interactionName);
        }
        if (myParser.isInteractionRepeat(interactionName)) {
            throw new InteractionDuplicatedException(interactionName);
        }
        return myParser.getParticipantCount(interactionName);
    }

    @Override
    public UmlLifeline getParticipantCreator(String interactionName, String lifelineName)
            throws InteractionNotFoundException, InteractionDuplicatedException,
            LifelineNotFoundException, LifelineDuplicatedException,
            LifelineNeverCreatedException, LifelineCreatedRepeatedlyException {
        if (!myParser.isInteractionExist(interactionName)) {
            throw new InteractionNotFoundException(interactionName);
        }
        if (myParser.isInteractionRepeat(interactionName)) {
            throw new InteractionDuplicatedException(interactionName);
        }
        if (!myParser.isLifelineExist(interactionName, lifelineName)) {
            throw new LifelineNotFoundException(interactionName, lifelineName);
        }
        if (myParser.isLifelineRepeat(interactionName, lifelineName)) {
            throw new LifelineDuplicatedException(interactionName, lifelineName);
        }
        if (!myParser.isLifelineCreateExist(interactionName, lifelineName)) {
            throw new LifelineNeverCreatedException(interactionName, lifelineName);
        }
        if (myParser.isLifelineCreateRepeat(interactionName, lifelineName)) {
            throw new LifelineCreatedRepeatedlyException(interactionName, lifelineName);
        }

        return myParser.getParticipantCreator(interactionName, lifelineName);
    }

    @Override
    public Pair<Integer, Integer> getParticipantLostAndFound(String interactionName,
                                                             String lifelineName)
            throws InteractionNotFoundException, InteractionDuplicatedException,
            LifelineNotFoundException, LifelineDuplicatedException {
        if (!myParser.isInteractionExist(interactionName)) {
            throw new InteractionNotFoundException(interactionName);
        }
        if (myParser.isInteractionRepeat(interactionName)) {
            throw new InteractionDuplicatedException(interactionName);
        }
        if (!myParser.isLifelineExist(interactionName, lifelineName)) {
            throw new LifelineNotFoundException(interactionName, lifelineName);
        }
        if (myParser.isLifelineRepeat(interactionName, lifelineName)) {
            throw new LifelineDuplicatedException(interactionName, lifelineName);
        }
        return myParser.getParticipantLostAndFound(interactionName, lifelineName);
    }

    @Override
    public int getStateCount(String stateMachineName)
            throws StateMachineNotFoundException,
            StateMachineDuplicatedException {
        if (!myParser.isStateMachineExist(stateMachineName)) {
            throw new StateMachineNotFoundException(stateMachineName);
        }
        if (myParser.isStateMachineRepeat(stateMachineName)) {
            throw new StateMachineDuplicatedException(stateMachineName);
        }
        return myParser.getStateCount(stateMachineName);
    }

    @Override
    public boolean getStateIsCriticalPoint(String stateMachineName, String stateName)
            throws StateMachineNotFoundException, StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException {
        if (!myParser.isStateMachineExist(stateMachineName)) {
            throw new StateMachineNotFoundException(stateMachineName);
        }
        if (myParser.isStateMachineRepeat(stateMachineName)) {
            throw new StateMachineDuplicatedException(stateMachineName);
        }
        if (!myParser.isStateExist(stateMachineName, stateName)) {
            throw new StateNotFoundException(stateMachineName, stateName);
        }
        if (myParser.isStateRepeat(stateMachineName, stateName)) {
            throw new StateDuplicatedException(stateMachineName, stateName);
        }
        return myParser.getStateIsCriticalPoint(stateMachineName, stateName);
    }

    @Override
    public List<String> getTransitionTrigger(String stateMachineName, String sourceStateName,
                                             String targetStateName)
            throws StateMachineNotFoundException, StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException, TransitionNotFoundException {
        if (!myParser.isStateMachineExist(stateMachineName)) {
            throw new StateMachineNotFoundException(stateMachineName);
        }
        if (myParser.isStateMachineRepeat(stateMachineName)) {
            throw new StateMachineDuplicatedException(stateMachineName);
        }
        if (!myParser.isStateExist(stateMachineName, sourceStateName)) {
            throw new StateNotFoundException(stateMachineName, sourceStateName);
        }
        if (myParser.isStateRepeat(stateMachineName, sourceStateName)) {
            throw new StateDuplicatedException(stateMachineName, sourceStateName);
        }
        if (!myParser.isStateExist(stateMachineName, targetStateName)) {
            throw new StateNotFoundException(stateMachineName, targetStateName);
        }
        if (myParser.isStateRepeat(stateMachineName, targetStateName)) {
            throw new StateDuplicatedException(stateMachineName, targetStateName);
        }
        if (!myParser.isTransitionExist(stateMachineName, sourceStateName, targetStateName)) {
            throw new TransitionNotFoundException(
                    stateMachineName, sourceStateName, targetStateName);
        }
        return myParser.getTransitionTrigger(stateMachineName, sourceStateName, targetStateName);
    }

    // 第三次作业
    @Override
    public void checkForUml001() throws UmlRule001Exception {
        if (!myParser.uml001IsOK()) {
            throw new UmlRule001Exception();
        }
    }

    @Override
    public void checkForUml002() throws UmlRule002Exception {
        if (!myParser.uml002IsOK()) {
            HashSet<AttributeClassInformation> hashSet;
            hashSet = myParser.getUml002Error();
            throw new UmlRule002Exception(hashSet);
        }
    }

    @Override
    public void checkForUml003() throws UmlRule003Exception {
        if (!myParser.uml003IsOK()) {
            HashSet<UmlClassOrInterface> hashSet;
            hashSet = myParser.getUml003Error();
            throw new UmlRule003Exception(hashSet);
        }
    }

    @Override
    public void checkForUml004() throws UmlRule004Exception {
        if (!myParser.uml004IsOK()) {
            HashSet<UmlClassOrInterface> hashSet;
            hashSet = myParser.getUml004Error();
            throw new UmlRule004Exception(hashSet);
        }
    }

    @Override
    public void checkForUml005() throws UmlRule005Exception {
        if (!myParser.uml005IsOK()) {
            throw new UmlRule005Exception();
        }
    }

    @Override
    public void checkForUml006() throws UmlRule006Exception {
        if (!myParser.uml006IsOK()) {
            throw new UmlRule006Exception();
        }
    }

    @Override
    public void checkForUml007() throws UmlRule007Exception {
        if (!myParser.uml007IsOK()) {
            throw new UmlRule007Exception();
        }
    }

    @Override
    public void checkForUml008() throws UmlRule008Exception {
        if (!myParser.uml008IsOK()) {
            throw new UmlRule008Exception();
        }
    }

    @Override
    public void checkForUml009() throws UmlRule009Exception {
        if (!myParser.uml009IsOK()) {
            throw new UmlRule009Exception();
        }
    }

}
