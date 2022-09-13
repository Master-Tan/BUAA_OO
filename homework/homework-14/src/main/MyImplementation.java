package main;

import com.oocourse.uml2.interact.common.Pair;
import com.oocourse.uml2.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.InteractionDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.InteractionNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.LifelineCreatedRepeatedlyException;
import com.oocourse.uml2.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNeverCreatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.MethodDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.MethodWrongTypeException;
import com.oocourse.uml2.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.TransitionNotFoundException;
import com.oocourse.uml2.interact.format.UserApi;
import com.oocourse.uml2.models.common.Visibility;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.elements.UmlLifeline;

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
                    stateMachineName, sourceStateName,targetStateName);
        }
        return myParser.getTransitionTrigger(stateMachineName, sourceStateName, targetStateName);
    }
}
