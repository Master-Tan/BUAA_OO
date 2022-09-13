import com.oocourse.elevator3.PersonRequest;
import com.oocourse.elevator3.Request;

import java.util.Arrays;

public class MyRequest {

    private int fromFloor;
    private int toFloor;
    private char fromBuilding;
    private char toBuilding;
    private int personId;
    private int changeFloor;

    public MyRequest(Request request) {
        this.fromFloor = ((PersonRequest) request).getFromFloor();
        this.toFloor = ((PersonRequest) request).getToFloor();
        this.fromBuilding = ((PersonRequest) request).getFromBuilding();
        this.toBuilding = ((PersonRequest) request).getToBuilding();
        this.personId = ((PersonRequest) request).getPersonId();
        this.changeFloor = 1;
    }

    public MyRequest(int fromFloor, int toFloor,
                     String fromBuilding, String toBuilding, int personId) {
        this.fromFloor = fromFloor;
        this.toFloor = toFloor;
        this.fromBuilding = fromBuilding.charAt(0);
        this.toBuilding = toBuilding.charAt(0);
        this.personId = personId;
        this.changeFloor = 1;
    }

    /**
     * 获取出发楼层
     *
     * @return 出发楼层
     */
    public int getFromFloor() {
        return fromFloor;
    }

    /**
     * 获取目标楼层
     *
     * @return 目标楼层
     */
    public int getToFloor() {
        return toFloor;
    }

    /**
     * 获取出发楼座
     *
     * @return 出发楼座
     */
    public char getFromBuilding() {
        return fromBuilding;
    }

    /**
     * 获取目标楼座
     *
     * @return 目标楼座
     */
    public char getToBuilding() {
        return toBuilding;
    }

    /**
     * 获取人员id
     *
     * @return 人员id
     */
    public int getPersonId() {
        return personId;
    }

    /**
     * 转为字符串形式
     *
     * @return 字符串形式
     */
    @Override
    public String toString() {
        return String.format("%d-FROM-%c-%d-TO-%c-%d",
                personId, fromBuilding, fromFloor, toBuilding, toFloor);
    }

    /**
     * 获取哈希值
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Arrays.hashCode(new int[]{this.personId, this.fromFloor, this.toFloor,
            this.fromBuilding, this.toBuilding});
    }

    /**
     * 判断对象是否相等
     *
     * @param obj 对象
     * @return 是否相等
     */
    @Override
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        } else if (obj instanceof PersonRequest) {
            return (((PersonRequest) obj).getFromFloor() == this.fromFloor)
                    && (((PersonRequest) obj).getToFloor() == this.toFloor)
                    && (((PersonRequest) obj).getPersonId() == this.personId)
                    && (((PersonRequest) obj).getFromBuilding() == this.fromBuilding)
                    && (((PersonRequest) obj).getToBuilding() == this.toBuilding);
        } else {
            return false;
        }
    }

    public int getChangeFloor() {
        return changeFloor;
    }

    public void setChangeFloor(int changeFloor) {
        this.changeFloor = changeFloor;
    }

}
