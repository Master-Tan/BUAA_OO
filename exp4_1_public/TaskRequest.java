import java.util.Arrays;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TaskRequest {
    private final int id;
    private final double time;
    private boolean done;
    private static final String PARSE_PATTERN_STRING = "^ADD-(?<taskId>\\d+)-(?<taskTime>\\d*.?\\d+)$";
    private static final Pattern PARSE_PATTERN = Pattern.compile(PARSE_PATTERN_STRING);

    public TaskRequest(int id, double time) {
        this.id = id;
        this.time = time;
        this.done = false;
    }

    public String toString() {
        String ans = String.format("ADD-%d-%f", this.id, this.time);
        return ans;
    }

    public int hashCode() {
        return Arrays.hashCode(new String[]{String.valueOf(this.id)});
    }

    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        } else {
            return obj instanceof TaskRequest && ((TaskRequest) obj).id == this.id;
        }
    }

    public int getId() {
        return id;
    }

    public double getTime() {
        return time;
    }

    public boolean isDone() {
        return done;
    }

    public void setDone(boolean done) {
        this.done = done;
    }

    static TaskRequest parse(String string) {
        Matcher matcher = PARSE_PATTERN.matcher(string);
        if (matcher.matches()) {
            int id = Integer.parseInt(matcher.group("taskId"));
            double time = Double.parseDouble(matcher.group("taskTime"));
            return new TaskRequest(id, time);
        }
        return null;
    }
}
