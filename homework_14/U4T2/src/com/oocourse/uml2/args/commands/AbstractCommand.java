package com.oocourse.uml2.args.commands;

/**
 * 抽象指令
 */
public abstract class AbstractCommand {
    /**
     * 获取指令名称
     *
     * @return 指令名称
     */
    public abstract String getCommandName();

    /**
     * 运行指令
     *
     * @throws Exception 异常
     */
    public abstract void run() throws Exception;
}
