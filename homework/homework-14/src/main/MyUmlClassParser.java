package main;

import main.myumlclass.MyClass;
import main.myumlclass.MyClassOrInterface;
import main.myumlclass.MyInterface;
import main.myumlclass.MyOperation;
import main.myumlclass.MyParameter;
import com.oocourse.uml2.models.common.Direction;
import com.oocourse.uml2.models.common.Visibility;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

public class MyUmlClassParser {

    private HashMap<String, MyClassOrInterface> myClassOrInterfaces;
    private HashMap<String, MyOperation> myOperations;
    private HashMap<String, Integer> classNames;
    private HashMap<String, String> classNameToId;

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

    public MyUmlClassParser(HashMap<String, MyClassOrInterface> myClassOrInterfaces,
                            HashMap<String, MyOperation> myOperations,
                            HashMap<String, Integer> classNames,
                            HashMap<String, String> classNameToId) {

        this.myClassOrInterfaces = myClassOrInterfaces;
        this.myOperations = myOperations;
        this.classNames = classNames;
        this.classNameToId = classNameToId;

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
        if (operationRepeat.containsKey(className)) {
            if (operationRepeat.get(className).containsKey(methodName)) {
                return operationRepeat.get(className).get(methodName);
            } else {
                MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
                ArrayList<ArrayList<String>> operationsRef = new ArrayList<>();
                ArrayList<ArrayList<String>> operationsName = new ArrayList<>();
                for (MyOperation myOperation : myClass.getOperations().values()) {
                    if (methodName.equals(myOperation.getName())) {
                        ArrayList<String> parametersRef = new ArrayList<>();
                        ArrayList<String> parametersName = new ArrayList<>();
                        for (MyParameter parameter : myOperation.getParameters()) {
                            if (parameter.getDirection() == Direction.IN) {
                                if (parameter.getType().equals("ref")) {
                                    parametersRef.add(parameter.getReferenceId());
                                } else if (parameter.getType().equals("name")) {
                                    parametersName.add(parameter.getTypeName());
                                }
                            }
                        }
                        parametersRef.sort(Comparator.naturalOrder());
                        parametersName.sort(Comparator.naturalOrder());
                        for (int i = 0; i < operationsRef.size(); i++) {
                            if (operationsRef.get(i).equals(parametersRef) &&
                                    operationsName.get(i).equals(parametersName)) {
                                operationRepeat.get(className).put(methodName, true);
                                return true;
                            }
                        }
                        operationsRef.add(parametersRef);
                        operationsName.add(parametersName);
                    }
                }
                operationRepeat.get(className).put(methodName, false);
                return false;
            }
        } else {
            return op1(myClassOrInterfaces, classNameToId, className, methodName);
        }
    }

    private boolean op1(HashMap<String, MyClassOrInterface> myClassOrInterfaces,
                               HashMap<String, String> classNameToId, String className,
                               String methodName) {
        MyClass myClass = ((MyClass) myClassOrInterfaces.get(classNameToId.get(className)));
        ArrayList<ArrayList<String>> operationsRef = new ArrayList<>();
        ArrayList<ArrayList<String>> operationsName = new ArrayList<>();
        for (MyOperation myOperation : myClass.getOperations().values()) {
            if (myOperation.getName() != null) {
                if (myOperation.getName().equals(methodName)) {
                    ArrayList<String> parametersRef = new ArrayList<>();
                    ArrayList<String> parametersName = new ArrayList<>();
                    for (MyParameter parameter : myOperation.getParameters()) {
                        if (parameter.getDirection() == Direction.IN) {
                            if (parameter.getType().equals("ref")) {
                                parametersRef.add(parameter.getReferenceId());
                            } else if (parameter.getType().equals("name")) {
                                parametersName.add(parameter.getTypeName());
                            }
                        }
                    }
                    parametersRef.sort(Comparator.naturalOrder());
                    parametersName.sort(Comparator.naturalOrder());
                    for (int i = 0; i < operationsRef.size(); i++) {
                        if (operationsRef.get(i).equals(parametersRef) &&
                                operationsName.get(i).equals(parametersName)) {
                            return true;
                        }
                    }
                    operationsRef.add(parametersRef);
                    operationsName.add(parametersName);
                }
            }
        }
        return false;
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
