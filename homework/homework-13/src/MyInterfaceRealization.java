import com.oocourse.uml1.models.elements.UmlInterfaceRealization;

public class MyInterfaceRealization extends MyElement {

    private String sourse;
    private String target;

    public MyInterfaceRealization(UmlInterfaceRealization umlInterfaceRealization) {

        super(umlInterfaceRealization);

        this.sourse = umlInterfaceRealization.getSource();
        this.target = umlInterfaceRealization.getTarget();

    }

    public String getSourse() {
        return sourse;
    }

    public String getTarget() {
        return target;
    }
}