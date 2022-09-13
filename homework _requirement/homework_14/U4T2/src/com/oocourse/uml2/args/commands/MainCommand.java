package com.oocourse.uml2.args.commands;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.oocourse.uml2.configs.Version;
import com.oocourse.uml2.utils.common.RunnableWithException;

import java.util.Calendar;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * 主解析
 */
@SuppressWarnings({"FieldCanBeLocal", "WeakerAccess"})
public class MainCommand extends AbstractCommand {
    private final Map<ProcessType, RunnableWithException> PROCESSES
            = Collections.unmodifiableMap(new HashMap<ProcessType, RunnableWithException>() {{
        put(ProcessType.HELP, MainCommand.this::processHelp);
        put(ProcessType.VERSION, MainCommand.this::processVersion);
    }});
    private final RunnableWithException DEFAULT_PROCESS = this::processHelp;
    /**
     * 帮助选项
     */
    @Parameter(names = {"--help", "-h"}, help = true, description = "Show the help information.")
    private boolean help = false;
    /**
     * 查看版本信息
     */
    @Parameter(names = {"--version", "-v"}, help = true, description = "Show the version information.")
    private boolean version = false;

    /**
     * 是否为帮助选项
     *
     * @return 是否为帮助选项
     */
    public boolean isHelp() {
        return help;
    }

    /**
     * 是否查看版本信息
     *
     * @return 版本信息
     */
    public boolean isVersion() {
        return version;
    }

    /**
     * 获取命令名称
     *
     * @return 命令名称
     */
    @Override
    public String getCommandName() {
        return null;
    }

    /**
     * 运行命令
     *
     * @throws Exception 异常信息
     */
    @Override
    public void run() throws Exception {
        ProcessType type = getProcessType();
        PROCESSES.getOrDefault(type, DEFAULT_PROCESS).run();
    }

    /**
     * 获取处理类型
     *
     * @return 处理类型
     */
    private ProcessType getProcessType() {
        if (isHelp()) {
            return ProcessType.HELP;
        } else if (isVersion()) {
            return ProcessType.VERSION;
        } else {
            return null;
        }
    }

    /**
     * 帮助信息
     */
    private void processHelp() {
        new JCommander(this).usage();
    }

    /**
     * 版本信息
     */
    private void processVersion() {
        System.out.println(String.format("%s, version %s.", Version.ARTIFACT_ID, Version.VERSION_ID));
        System.out.println(String.format("©2019-%s %s, Inc. All rights reserved.",
                Calendar.getInstance().get(Calendar.YEAR),
                Version.GROUP_ID
        ));
    }

    /**
     * 处理类型
     */
    private enum ProcessType {
        HELP,
        VERSION,
    }
}
