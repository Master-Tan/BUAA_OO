import com.oocourse.uml1.models.elements.UmlElement;

public class MyElement {

    private String parentId;
    private String id;
    private String name;

    public MyElement(UmlElement umlElement) {

        this.parentId = umlElement.getParentId();
        this.id = umlElement.getId();
        this.name = umlElement.getName();

    }

    public String getParentId() {
        return parentId;
    }

    public String getId() {
        return id;
    }

    public String getName() {
        return name;
    }

}
