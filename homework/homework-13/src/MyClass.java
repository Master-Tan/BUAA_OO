import com.oocourse.uml1.models.common.Visibility;
import com.oocourse.uml1.models.elements.UmlClass;

import java.util.HashSet;

public class MyClass extends MyClassOrInterface {

    private Visibility visibility;

    private HashSet<MyInterface> realizeInterfaces = new HashSet<>();

    public MyClass(UmlClass umlClass) {

        super(umlClass);

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
