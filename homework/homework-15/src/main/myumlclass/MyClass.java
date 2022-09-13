package main.myumlclass;

import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlClass;

import java.util.HashSet;

public class MyClass extends MyClassOrInterface {

    private Visibility visibility;

    private HashSet<MyInterface> realizeInterfaces = new HashSet<>();

    public MyClass(UmlClass umlClass,
                   HashSet<MyClassOrInterface> uml003Error,
                   HashSet<MyClassOrInterface> uml004Error) {

        super(umlClass, uml003Error, uml004Error);

        this.visibility = umlClass.getVisibility();

    }

    public void classRealize(MyInterface target) {
        for (MyClassOrInterface myChildClass : this.getChildren().keySet()) {
            for (MyClassOrInterface myParentInterface : target.getParents().keySet()) {
                ((MyClass) myChildClass).getRealizeInterfaces().add(
                        ((MyInterface) myParentInterface));
            }
        }
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public HashSet<MyInterface> getRealizeInterfaces() {
        return realizeInterfaces;
    }
}
