import com.oocourse.uml1.models.common.Direction;
import com.oocourse.uml1.models.common.Visibility;
import com.oocourse.uml1.models.elements.UmlAssociation;
import com.oocourse.uml1.models.elements.UmlAssociationEnd;
import com.oocourse.uml1.models.elements.UmlAttribute;
import com.oocourse.uml1.models.elements.UmlClass;
import com.oocourse.uml1.models.elements.UmlElement;
import com.oocourse.uml1.models.elements.UmlGeneralization;
import com.oocourse.uml1.models.elements.UmlInterface;
import com.oocourse.uml1.models.elements.UmlInterfaceRealization;
import com.oocourse.uml1.models.elements.UmlOperation;
import com.oocourse.uml1.models.elements.UmlParameter;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

public class MyParser {

    private int length;
    private ArrayList<UmlElement> elements = new ArrayList<>();
    private HashMap<String, MyClassOrInterface> myClassOrInterfaces = new HashMap<>();
    private HashMap<String, MyOperation> myOperations = new HashMap<>();
    private HashMap<String, Integer> classNames = new HashMap<>();
    private HashMap<String, String> classNameToId = new HashMap<>();

    // 动态维护
    private int classCount = -1;
    private HashMap<String, Integer> classSubclassCount = new HashMap<>();
    private HashMap<String, Integer> operationCount = new HashMap<>();
    private HashMap<String, HashMap<String, Map<Visibility, Integer>>> classOperationVisibility =
            new HashMap<>();
    private HashMap<String, HashMap<String, Boolean>> operationWrongType =
            new HashMap<>();
    private HashMap<String, HashMap<String, Boolean>> operationRepeat =
            new HashMap<>();
    private HashMap<String, HashMap<String, List<Integer>>> classOperationCouplingDegree =
            new HashMap<>();
    private HashMap<String, Integer> classAttributeCouplingDegree = new HashMap<>();
    private HashMap<String, List<String>> classImplementInterfaceList = new HashMap<>();
    private HashMap<String, Integer> classDepthOfInheritance = new HashMap<>();

    public MyParser(UmlElement... elements) {

        this.length = elements.length;

        for (int i = 0; i < length; i++) {
            this.elements.add(elements[i]);
            //            System.out.println("\n" + elements[i].toJson().get("target"));
            //            System.out.println(elements[i].toJson());
            //            System.out.println(elements[i].getClass().getSimpleName());
        }

        /*
            设计三个独立的循环
            第一轮处理 UML_CLASS、UML_INTERFACE、UML_ASSOCIATION
            第二轮处理 UML_ATTRIBUTE、UML_OPERATION、UML_ASSOCIATION_END、UML_GENERALIZATION
            第三轮处理 UML_PARAMETER、UML_INTERFACE_REALIZATION
        */

        this.initRound1();
        this.initRound2();
        this.initRound3();

    }

    private void initRound1() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_CLASS: {
                    UmlClass umlClass = (UmlClass) element;
                    MyClass myClass = new MyClass(umlClass);
                    myClassOrInterfaces.put(myClass.getId(), myClass);
                    if (!classNames.containsKey(myClass.getName())) {
                        classNames.put(myClass.getName(), 1);
                    } else {
                        classNames.put(myClass.getName(), classNames.get(myClass.getName()) + 1);
                    }
                    classNameToId.put(myClass.getName(), myClass.getId());
                    break;
                }
                case UML_INTERFACE: {
                    UmlInterface umlInterface = (UmlInterface) element;
                    MyInterface myInterface = new MyInterface(umlInterface);
                    myClassOrInterfaces.put(myInterface.getId(), myInterface);
                    break;
                }
                case UML_ASSOCIATION: {
                    UmlAssociation umlAssociation = (UmlAssociation) element;
                    MyAssociation myAssociation = new MyAssociation(umlAssociation);
                    break;
                }
                default:
                    break;
            }
        }
    }

    private void initRound2() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_ATTRIBUTE: {
                    UmlAttribute umlAttribute = (UmlAttribute) element;
                    MyAttribute myAttribute = new MyAttribute(umlAttribute);
                    MyClassOrInterface myElement =
                            myClassOrInterfaces.get(myAttribute.getParentId());
                    myElement.addAttribute(myAttribute);
                    break;
                }
                case UML_OPERATION: {
                    UmlOperation umlOperation = (UmlOperation) element;
                    MyOperation myOperation = new MyOperation(umlOperation);
                    MyClassOrInterface myElement =
                            myClassOrInterfaces.get(myOperation.getParentId());
                    myElement.addOperation(myOperation);
                    this.myOperations.put(myOperation.getId(), myOperation);
                    break;
                }
                case UML_ASSOCIATION_END: {
                    UmlAssociationEnd umlAssociationEnd = (UmlAssociationEnd) element;
                    MyAssociationEnd myAssociationEnd = new MyAssociationEnd(umlAssociationEnd);
                    break;
                }
                case UML_GENERALIZATION: {
                    UmlGeneralization umlGeneralization = (UmlGeneralization) element;
                    MyGeneralization myGeneralization = new MyGeneralization(umlGeneralization);
                    MyClassOrInterface parent =
                            myClassOrInterfaces.get(myGeneralization.getTarget());
                    MyClassOrInterface child =
                            myClassOrInterfaces.get(myGeneralization.getSourse());
                    parent.addChild(child);
                    child.addParent(parent);
                    break;
                }
                default:
                    break;
            }
        }
    }

    private void initRound3() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_PARAMETER: {
                    UmlParameter umlParameter = (UmlParameter) element;
                    MyParameter myParameter = new MyParameter(umlParameter);
                    MyOperation myOperation = this.myOperations.get(umlParameter.getParentId());
                    myOperation.addParameter(myParameter);
                    break;
                }
                case UML_INTERFACE_REALIZATION: {
                    UmlInterfaceRealization umlInterfaceRealization =
                            (UmlInterfaceRealization) element;
                    MyInterfaceRealization myInterfaceRealization =
                            new MyInterfaceRealization(umlInterfaceRealization);
                    MyClass source =
                            ((MyClass) myClassOrInterfaces.get(myInterfaceRealization.getSourse()));
                    MyInterface target = ((MyInterface)
                            myClassOrInterfaces.get(myInterfaceRealization.getTarget()));
                    source.classRealize(target);
                    target.interfaceRealize(source);
                    break;
                }
                default:
                    break;
            }
        }
    }

    public int getClassCount() {
        if (classCount == -1) {
            classCount = 0;
            for (MyClassOrInterface myClassOrInterface : this.myClassOrInterfaces.values()) {
                if (myClassOrInterface instanceof MyClass) {
                    classCount++;
                }
            }
        }
        return classCount;
    }

    public boolean isClassExist(String className) {
        return classNames.containsKey(className);
    }

    public boolean isClassRepeat(String className) {
        if (classNames.containsKey(className)) {
            if (classNames.get(className) > 1) {
                return true;
            }
        }
        return false;
    }

    public int getClassSubclassCount(String className) {
        int count;
        if (!classSubclassCount.containsKey(className)) {
            count = 0;
            MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
            for (MyClassOrInterface classOrInterface :
                    myClass.getChildren().keySet()) {
                if (myClass.getChildren().get(classOrInterface) == 1) {
                    count++;
                }
            }
            classSubclassCount.put(className, count);
        } else {
            count = classSubclassCount.get(className);
        }
        return count;
    }

    public int getOperationCount(String className) {
        int count;
        if (!operationCount.containsKey(className)) {
            MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
            count = myClass.getOperations().size();
            operationCount.put(className, count);
        } else {
            count = operationCount.get(className);
        }
        return count;
    }

    public Map<Visibility, Integer> getClassOperationVisibility(
            String className, String methodName) {
        Map<Visibility, Integer> map = new HashMap<>();
        if (classOperationVisibility.containsKey(className)) {
            if (classOperationVisibility.get(className).containsKey(methodName)) {
                map = classOperationVisibility.get(className).get(methodName);
            } else {
                map.put(Visibility.PUBLIC, 0);
                map.put(Visibility.PACKAGE, 0);
                map.put(Visibility.PRIVATE, 0);
                map.put(Visibility.PROTECTED, 0);
                MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
                for (MyOperation myOperation : myClass.getOperations().values()) {
                    if (myOperation.getName() == null) {
                        continue;
                    } else if (myOperation.getName().equals(methodName)) {
                        Visibility myVisibility = myOperation.getVisibility();
                        map.put(myVisibility,
                                map.get(myVisibility) + 1);
                    }
                }
                classOperationVisibility.get(className).put(methodName, map);
            }
        } else {
            map.put(Visibility.PUBLIC, 0);
            map.put(Visibility.PACKAGE, 0);
            map.put(Visibility.PRIVATE, 0);
            map.put(Visibility.PROTECTED, 0);
            MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
            for (MyOperation myOperation : myClass.getOperations().values()) {
                if (myOperation.getName() == null) {
                    continue;
                } else if (myOperation.getName().equals(methodName)) {
                    Visibility myVisibility = myOperation.getVisibility();
                    map.put(myVisibility,
                            map.get(myVisibility) + 1);
                }
            }
            HashMap<String, Map<Visibility, Integer>> hashMap = new HashMap<>();
            hashMap.put(methodName, map);
            classOperationVisibility.put(className, hashMap);
        }
        return map;
    }

    public boolean isOperationWrongType(String className, String methodName) {
        if (operationWrongType.containsKey(className)) {
            if (operationWrongType.get(className).containsKey(methodName)) {
                return operationWrongType.get(className).get(methodName);
            } else {
                MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
                for (MyOperation myOperation : myClass.getOperations().values()) {
                    if (myOperation.getName() != null) {
                        if (myOperation.getName().equals(methodName)) {
                            for (MyParameter parameter : myOperation.getParameters()) {
                                if (!(parameter.getType().equals("name"))) {
                                    continue;
                                }
                                String typeName = parameter.getTypeName();
                                if (typeName.equals("void") && parameter.getDirection() ==
                                        Direction.RETURN) { continue; }
                                if (!Arrays.asList("byte", "short", "int", "long", "float",
                                        "double", "char", "boolean", "String").contains(typeName)) {
                                    operationWrongType.get(className).put(methodName, true);
                                    return true;
                                }
                            }
                        }
                    }
                }
                operationWrongType.get(className).put(methodName, false);
                return false;
            }
        } else {
            MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
            for (MyOperation myOperation : myClass.getOperations().values()) {
                if (myOperation.getName() != null) {
                    if (myOperation.getName().equals(methodName)) {
                        for (MyParameter parameter : myOperation.getParameters()) {
                            if (!(parameter.getType().equals("name"))) {
                                continue;
                            }
                            String typeName = parameter.getTypeName();
                            if (typeName.equals("void") && parameter.getDirection() ==
                                    Direction.RETURN) {
                                continue;
                            }
                            if (!Arrays.asList("byte", "short", "int", "long", "float", "double",
                                    "char", "boolean", "String").contains(typeName)) {
                                HashMap<String, Boolean> hashMap = new HashMap<>();
                                hashMap.put(methodName, true);
                                operationWrongType.put(className, hashMap);
                                return true;
                            }
                        }
                    }
                }
            }
            HashMap<String, Boolean> hashMap = new HashMap<>();
            hashMap.put(methodName, false);
            operationWrongType.put(className, hashMap);
            return false;
        }
    }

    public boolean isOperationRepeat(String className, String methodName) {
        return MyParser2.isOperationRepeat(className, methodName, myClassOrInterfaces,
                classNameToId);
    }

    public List<Integer> getClassOperationCouplingDegree(
            String className, String methodName) {
        List<Integer> list = new ArrayList<>();
        if (classOperationCouplingDegree.containsKey(className)) {
            if (classOperationCouplingDegree.get(className).containsKey(methodName)) {
                list = classOperationCouplingDegree.get(className).get(methodName);
            } else {
                MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
                ArrayList<ArrayList<String>> operations = new ArrayList<>();
                for (MyOperation myOperation : myClass.getOperations().values()) {
                    if (myOperation.getName() != null) {
                        if (myOperation.getName().equals(methodName)) {
                            HashSet<String> parameters = new HashSet<>();
                            for (MyParameter parameter : myOperation.getParameters()) {
                                if (parameter.getType().equals("ref") &&
                                        !myOperation.getParentId().equals(
                                                parameter.getReferenceId())) {
                                    parameters.add(parameter.getReferenceId());
                                }
                            }
                            list.add(parameters.size());
                        }
                    }
                }
                classOperationCouplingDegree.get(className).put(methodName, list);
            }
        } else {
            MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
            ArrayList<ArrayList<String>> operations = new ArrayList<>();
            for (MyOperation myOperation : myClass.getOperations().values()) {
                if (myOperation.getName() != null) {
                    if (myOperation.getName().equals(methodName)) {
                        HashSet<String> parameters = new HashSet<>();
                        for (MyParameter parameter : myOperation.getParameters()) {
                            if (parameter.getType().equals("ref")) {
                                if (!parameter.getReferenceId().equals(myOperation.getParentId())) {
                                    parameters.add(parameter.getReferenceId());
                                }
                            }
                        }
                        list.add(parameters.size());

                    }
                }
            }
            HashMap<String, List<Integer>> hashMap = new HashMap<>();
            hashMap.put(methodName, list);
            classOperationCouplingDegree.put(className, hashMap);
        }
        return list;
    }

    public int getClassAttributeCouplingDegree(String className) {
        int count;
        if (classAttributeCouplingDegree.containsKey(className)) {
            count = classAttributeCouplingDegree.get(className);
        } else {
            MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
            HashSet<String> attributes = new HashSet<>();
            for (MyClassOrInterface myClassOrInterface : myClass.getParents().keySet()) {
                for (MyAttribute myAttribute : myClassOrInterface.getAttributes().values()) {
                    if (myAttribute.getType().equals("ref")) {
                        if (!myAttribute.getReferenceId().equals(myClass.getId())) {
                            attributes.add(myAttribute.getReferenceId());
                        }
                    }
                }
            }
            count = attributes.size();
            classAttributeCouplingDegree.put(className, count);
        }
        return count;
    }

    public List<String> getClassImplementInterfaceList(String className) {
        List<String> list = new ArrayList<>();
        if (classImplementInterfaceList.containsKey(className)) {
            list = classImplementInterfaceList.get(className);
        } else {
            HashSet<String> check = new HashSet<>();
            MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
            for (MyInterface realizeInterface : myClass.getRealizeInterfaces()) {
                if (!check.contains(realizeInterface.getName())) {
                    check.add(realizeInterface.getName());
                    list.add(realizeInterface.getName());
                }
            }
            classImplementInterfaceList.put(className, list);
        }
        return list;
    }

    public int getClassDepthOfInheritance(String className) {
        int count = 0;
        if (classDepthOfInheritance.containsKey(className)) {
            count = classDepthOfInheritance.get(className);
        } else {
            MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
            for (Integer value : myClass.getParents().values()) {
                if (value > count) {
                    count = value;
                }
            }
            classDepthOfInheritance.put(className, count);
        }
        return count;
    }

}
