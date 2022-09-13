package main;

import com.oocourse.uml3.models.elements.UmlAssociation;
import com.oocourse.uml3.models.elements.UmlAssociationEnd;
import com.oocourse.uml3.models.elements.UmlAttribute;
import com.oocourse.uml3.models.elements.UmlClass;
import com.oocourse.uml3.models.elements.UmlClassOrInterface;
import com.oocourse.uml3.models.elements.UmlElement;
import com.oocourse.uml3.models.elements.UmlGeneralization;
import com.oocourse.uml3.models.elements.UmlInterface;
import com.oocourse.uml3.models.elements.UmlInterfaceRealization;
import com.oocourse.uml3.models.elements.UmlOperation;
import com.oocourse.uml3.models.elements.UmlParameter;
import main.myumlclass.MyAssociation;
import main.myumlclass.MyAssociationEnd;
import main.myumlclass.MyClass;
import main.myumlclass.MyClassOrInterface;
import main.myumlclass.MyGeneralization;
import main.myumlclass.MyInterface;
import main.myumlclass.MyInterfaceRealization;
import main.myumlclass.MyOperation;
import main.myumlclass.MyParameter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class MyUmlClassParserInit {

    private ArrayList<UmlElement> elements;
    private ArrayList<MyElement> myElements;

    private HashMap<String, MyClassOrInterface> myClassOrInterfaces = new HashMap<>();
    private HashMap<String, UmlClassOrInterface> umlClassOrInterface = new HashMap<>();
    private HashMap<String, MyOperation> myOperations = new HashMap<>();
    private HashMap<String, Integer> classNames = new HashMap<>();
    private HashMap<String, String> classNameToId = new HashMap<>();
    private HashMap<String, MyAssociation> myAssociations = new HashMap<>();
    private HashMap<String, MyAssociationEnd> myAssociationEnds = new HashMap<>();
    private HashSet<MyClassOrInterface> uml003Error;
    private HashSet<MyClassOrInterface> uml004Error;

    public MyUmlClassParserInit(ArrayList<UmlElement> elements, ArrayList<MyElement> myElements,
                                HashSet<MyClassOrInterface> uml003Error,
                                HashSet<MyClassOrInterface> uml004Error) {

        this.elements = elements;
        this.myElements = myElements;
        this.uml003Error = uml003Error;
        this.uml004Error = uml004Error;

        /*
            UMLClass：
            设计三个独立的循环
            第一轮处理 UML_CLASS、UML_INTERFACE
            第二轮处理 UML_ATTRIBUTE、UML_OPERATION、UML_ASSOCIATION_END、UML_GENERALIZATION
            第三轮处理 UML_PARAMETER、UML_INTERFACE_REALIZATION、UML_ASSOCIATION
        */

        this.umlClassInitRound1();
        this.umlClassInitRound2();
        this.umlClassInitRound3();

    }

    private void umlClassInitRound1() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_CLASS: {
                    UmlClass umlClass = (UmlClass) element;
                    MyClass myClass = new MyClass(umlClass, uml003Error, uml004Error);
                    myElements.add(myClass);
                    myClassOrInterfaces.put(myClass.getId(), myClass);
                    umlClassOrInterface.put(umlClass.getId(), umlClass);
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
                    MyInterface myInterface = new MyInterface(umlInterface,
                            uml003Error, uml004Error);
                    myElements.add(myInterface);
                    myClassOrInterfaces.put(myInterface.getId(), myInterface);
                    umlClassOrInterface.put(umlInterface.getId(), umlInterface);
                    break;
                }
                default: break;
            }
        }
    }

    private void umlClassInitRound2() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_ATTRIBUTE: {
                    UmlAttribute umlAttribute = (UmlAttribute) element;
                    MyAttribute myAttribute = new MyAttribute(umlAttribute);
                    myElements.add(myAttribute);
                    if (myClassOrInterfaces.containsKey(myAttribute.getParentId())) {
                        MyClassOrInterface myClassOrInterface =
                                myClassOrInterfaces.get(myAttribute.getParentId());
                        myClassOrInterface.addAttribute(myAttribute);
                    }
                    break;
                }
                case UML_OPERATION: {
                    UmlOperation umlOperation = (UmlOperation) element;
                    MyOperation myOperation = new MyOperation(umlOperation);
                    myElements.add(myOperation);
                    MyClassOrInterface myElement =
                            myClassOrInterfaces.get(myOperation.getParentId());
                    myElement.addOperation(myOperation);
                    this.myOperations.put(myOperation.getId(), myOperation);
                    break;
                }
                case UML_ASSOCIATION_END: {
                    UmlAssociationEnd umlAssociationEnd = (UmlAssociationEnd) element;
                    MyAssociationEnd myAssociationEnd = new MyAssociationEnd(umlAssociationEnd);
                    myElements.add(myAssociationEnd);
                    myAssociationEnds.put(myAssociationEnd.getId(), myAssociationEnd);
                    break;
                }
                case UML_GENERALIZATION: {
                    UmlGeneralization umlGeneralization = (UmlGeneralization) element;
                    MyGeneralization myGeneralization = new MyGeneralization(umlGeneralization);
                    myElements.add(myGeneralization);
                    MyClassOrInterface parent =
                            myClassOrInterfaces.get(myGeneralization.getTarget());
                    MyClassOrInterface child =
                            myClassOrInterfaces.get(myGeneralization.getSourse());
                    parent.addChild(child);
                    child.addParent(parent);
                    break;
                }
                default: break;
            }
        }
    }

    private void umlClassInitRound3() {
        for (UmlElement element : elements) {
            switch (element.getElementType()) {
                case UML_PARAMETER: {
                    UmlParameter umlParameter = (UmlParameter) element;
                    MyParameter myParameter = new MyParameter(umlParameter);
                    myElements.add(myParameter);
                    MyOperation myOperation = this.myOperations.get(umlParameter.getParentId());
                    myOperation.addParameter(myParameter);
                    break;
                }
                case UML_INTERFACE_REALIZATION: {
                    UmlInterfaceRealization umlInterfaceRealization =
                            (UmlInterfaceRealization) element;
                    MyInterfaceRealization myInterfaceRealization =
                            new MyInterfaceRealization(umlInterfaceRealization);
                    myElements.add(myInterfaceRealization);
                    MyClass source =
                            ((MyClass) myClassOrInterfaces.get(myInterfaceRealization.getSourse()));
                    MyInterface target = ((MyInterface)
                            myClassOrInterfaces.get(myInterfaceRealization.getTarget()));
                    source.classRealize(target);
                    target.interfaceRealize(source);
                    break;
                }
                case UML_ASSOCIATION: {
                    UmlAssociation umlAssociation = (UmlAssociation) element;
                    MyAssociation myAssociation = new MyAssociation(umlAssociation);
                    myElements.add(myAssociation);
                    myAssociations.put(myAssociation.getId(), myAssociation);
                    break;
                }
                default: break;
            }
        }
    }

    public HashMap<String, MyAssociation> getMyAssociations() {
        return myAssociations;
    }

    public HashMap<String, MyAssociationEnd> getMyAssociationEnds() {
        return myAssociationEnds;
    }

    public ArrayList<UmlElement> getElements() {
        return elements;
    }

    public HashMap<String, MyClassOrInterface> getMyClassOrInterfaces() {
        return myClassOrInterfaces;
    }

    public HashMap<String, UmlClassOrInterface> getUmlClassOrInterface() {
        return umlClassOrInterface;
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
}
