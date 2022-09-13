import com.oocourse.uml1.models.common.Visibility;
import com.oocourse.uml1.models.elements.UmlOperation;

import java.util.ArrayList;

public class MyOperation extends MyElement {

    private Visibility visibility;
    private ArrayList<MyParameter> parameters = new ArrayList<>();

    public MyOperation(UmlOperation umlOperation) {

        super(umlOperation);

        this.visibility = umlOperation.getVisibility();

    }

    public void addParameter(MyParameter myParameter) {
        this.parameters.add(myParameter);
    }

    public Visibility getVisibility() {
        return visibility;
    }

    public ArrayList<MyParameter> getParameters() {
        return parameters;
    }
}
