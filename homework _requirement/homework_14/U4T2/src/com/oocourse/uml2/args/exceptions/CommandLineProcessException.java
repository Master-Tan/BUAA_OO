package com.oocourse.uml2.args.exceptions;

/**
 * 命令行执行异常
 */
public class CommandLineProcessException extends Exception {
    private final int exitCode;

    /**
     * 构造函数
     *
     * @param message 错误信息
     */
    public CommandLineProcessException(int exitCode, String message) {
        super(message);
        this.exitCode = exitCode;
    }

    /**
     * 获取退出码
     *
     * @return 退出码
     */
    public int getExitCode() {
        return exitCode;
    }
}
