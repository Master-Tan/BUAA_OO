import com.oocourse.uml1.models.common.Direction;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;

public class MyParser2 {

    private static HashMap<String, HashMap<String, Boolean>> operationRepeat = new HashMap<>();

    public static boolean isOperationRepeat(String className, String methodName,
                                            HashMap<String, MyClassOrInterface> myClassOrInterfaces,
                                            HashMap<String, String> classNameToId) {
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

    private static boolean op1(HashMap<String, MyClassOrInterface> myClassOrInterfaces,
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

}
