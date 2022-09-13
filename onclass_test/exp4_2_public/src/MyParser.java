public class MyParser {
    private final String requestCode;
    private final int pipelineLength;
    private final String[] workingStages;

    MyParser(String request) {
        String[] temp = request.split(":"); //分离 requestCode
        requestCode = temp[0];
        workingStages = temp[1].split("-"); //分离工序
        pipelineLength = workingStages.length;
    }

    public String getRequestCode() {
        return requestCode;
    }

    public int getPipelineLength() {
        return pipelineLength;
    }

    public String[] getWorkingStages() {
        return workingStages;
    }
}
