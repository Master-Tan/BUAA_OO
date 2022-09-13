import java.util.BitSet;

public enum WorkingStage { //工序的枚举类，提供返回对应工作时间的方法
    Welding(800, 0),
    Polishing(200, 1),
    Assembling(400, 2),
    Packing(100, 3);

    private final int workingTime;
    private final BitSet mask;
    public static final int STAGE_NUM = 4; //工序的总数

    WorkingStage(int workingTime, int mask) {
        this.workingTime = workingTime;
        this.mask = new BitSet(STAGE_NUM);
        this.mask.set(mask);
    }

    public int getWorkingTime() {
        return workingTime;
    }

    public BitSet getMask() { //返回工序对应的掩码值
        return mask;
    }
}
