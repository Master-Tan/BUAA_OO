import com.oocourse.uml1.models.elements.UmlElement;

import java.util.HashMap;

public class MyClassOrInterface extends MyElement {

    private HashMap<String, MyAttribute> attributes = new HashMap<>();
    private HashMap<String, MyOperation> operations = new HashMap<>();

    private HashMap<MyClassOrInterface, Integer> parents = new HashMap<>();
    private HashMap<MyClassOrInterface, Integer> children = new HashMap<>();

    public MyClassOrInterface(UmlElement umlElement) {
        super(umlElement);
        children.put(this, 0);
        parents.put(this, 0);
    }

    public void addParent(MyClassOrInterface parent) {
        for (MyClassOrInterface myChildClassOrInterface : children.keySet()) {
            for (MyClassOrInterface myParentClassOrInterface : parent.getParents().keySet()) {
                if (myChildClassOrInterface.getParents().containsKey(myParentClassOrInterface)) {
                    if (myChildClassOrInterface.getParents().get(myParentClassOrInterface) >
                            myChildClassOrInterface.getParents().get(this) +
                                    parent.getParents().get(myParentClassOrInterface) + 1) {
                        myChildClassOrInterface.getParents().put(myParentClassOrInterface,
                                myChildClassOrInterface.getParents().get(this) +
                                        parent.getParents().get(myParentClassOrInterface) + 1);
                    }
                } else {
                    myChildClassOrInterface.getParents().put(myParentClassOrInterface,
                            myChildClassOrInterface.getParents().get(this) +
                                    parent.getParents().get(myParentClassOrInterface) + 1);
                }
            }
        }
    }

    public void addChild(MyClassOrInterface child) {
        for (MyClassOrInterface myParentClassOrInterface : parents.keySet()) {
            for (MyClassOrInterface myChildClassOrInterface : child.getChildren().keySet()) {
                if (myParentClassOrInterface.getChildren().containsKey(myChildClassOrInterface)) {
                    if ((myParentClassOrInterface.getChildren().get(myChildClassOrInterface)) >
                            myParentClassOrInterface.getChildren().get(this) +
                                    child.getChildren().get(myChildClassOrInterface) + 1) {
                        myParentClassOrInterface.getChildren().put(myChildClassOrInterface,
                                myParentClassOrInterface.getChildren().get(this) +
                                        child.getChildren().get(myChildClassOrInterface) + 1);
                    }
                } else {
                    myParentClassOrInterface.getChildren().put(myChildClassOrInterface,
                            myParentClassOrInterface.getChildren().get(this) +
                                    child.getChildren().get(myChildClassOrInterface) + 1);
                }
            }
        }
    }

    public void addOperation(MyOperation myOperation) {
        operations.put(myOperation.getId(), myOperation);
    }

    public void addAttribute(MyAttribute myAttribute) {
        attributes.put(myAttribute.getId(), myAttribute);
    }

    public HashMap<String, MyOperation> getOperations() {
        return operations;
    }

    public HashMap<String, MyAttribute> getAttributes() {
        return attributes;
    }

    public HashMap<MyClassOrInterface, Integer> getParents() {
        return parents;
    }

    public HashMap<MyClassOrInterface, Integer> getChildren() {
        return children;
    }
}
