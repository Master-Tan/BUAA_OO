import com.oocourse.uml1.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml1.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml1.interact.exceptions.user.MethodDuplicatedException;
import com.oocourse.uml1.interact.exceptions.user.MethodWrongTypeException;
import com.oocourse.uml1.interact.format.UserApi;
import com.oocourse.uml1.models.common.Visibility;
import com.oocourse.uml1.models.elements.UmlElement;

import java.util.List;
import java.util.Map;

public class MyImplementation implements UserApi {

    private MyParser myParser;

    public MyImplementation(UmlElement... elements) {
        myParser = new MyParser(elements);
    }

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
}
