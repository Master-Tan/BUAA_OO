package main.myumlclass;

import com.oocourse.uml3.models.common.Visibility;
import com.oocourse.uml3.models.elements.UmlInterface;

import java.util.HashSet;

public class MyInterface extends MyClassOrInterface {

    private Visibility visibility;

    private HashSet<MyClass> realizeClass = new HashSet<>();

    public MyInterface(UmlInterface umlInterface,
                       HashSet<MyClassOrInterface> uml003Error,
                       HashSet<MyClassOrInterface> uml004Error) {

        super(umlInterface, uml003Error, uml004Error);

        this.visibility = umlInterface.getVisibility();

    }

    public void interfaceRealize(MyClass source) {
        for (MyClassOrInterface myParentInterface : this.getParents().keySet()) {
            for (MyClassOrInterface myChildClass : source.getChildren().keySet()) {
                ((MyInterface) myParentInterface).getRealizeClass().add(((MyClass) myChildClass));
            }
        }
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public HashSet<MyClass> getRealizeClass() {
        return realizeClass;
    }
}
