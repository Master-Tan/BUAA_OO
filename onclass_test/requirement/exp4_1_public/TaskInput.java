import java.io.Closeable;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.Scanner;

public class TaskInput implements Closeable {
    private final Scanner scanner;
    private final HashSet<Integer> existedTaskId;
    private static final InputStream DEFAULT_INPUT_STREAM;

    public TaskInput(InputStream inputStream) {
        this.scanner = new Scanner(inputStream);
        this.existedTaskId = new HashSet();
    }

    public TaskInput() {
        this(DEFAULT_INPUT_STREAM);
    }

    public void close() throws IOException {
        this.scanner.close();
    }

    public TaskRequest nextRequest() {
        while(this.scanner.hasNextLine()) {
            String line = this.scanner.nextLine();

            TaskRequest request = TaskRequest.parse(line);

            this.existedTaskId.add(request.getId());
            return request;
        }
        return null;
    }

    static {
        DEFAULT_INPUT_STREAM = System.in;
    }
}

