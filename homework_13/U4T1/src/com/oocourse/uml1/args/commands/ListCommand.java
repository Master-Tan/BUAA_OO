package com.oocourse.uml1.args.commands;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.oocourse.uml1.args.validations.FileAccessibleValidation;
import com.oocourse.uml1.args.validations.TopModelTypeValidation;
import com.oocourse.uml1.models.top.StarumlFileTopModels;
import com.oocourse.uml1.models.top.TopModelType;
import com.oocourse.uml1.utils.common.RunnableWithException;
import com.oocourse.uml1.utils.json.InputWithJson;
import com.oocourse.uml1.utils.json.JsonLoadException;
import com.oocourse.uml1.utils.string.StringUtils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * 列表命令解析
 */
@SuppressWarnings({"FieldCanBeLocal", "WeakerAccess"})
public class ListCommand extends AbstractCommand {
    private static final String TYPE_TITLE = "Type";
    private static final String NAME_TITLE = "Name";
    private final RunnableWithException DEFAULT_PROCESS = this::processHelp;
    /**
     * 源代码路径
     */
    @Parameter(names = {"--source", "-s"}, description = "Set the path of the source code.",
            required = true, validateWith = FileAccessibleValidation.class)
    private String source;
    /**
     * 查询类别
     */
    @Parameter(names = {"--type", "-t"}, description = "Type of the source data (UMLModel supported only).",
            validateWith = TopModelTypeValidation.class)
    private String type = "UMLModel";
    private final Map<ProcessType, RunnableWithException> PROCESSES
            = Collections.unmodifiableMap(new HashMap<ProcessType, RunnableWithException>() {{
        put(ProcessType.HELP, ListCommand.this::processHelp);
        put(ProcessType.LIST, ListCommand.this::processList);
    }});
    /**
     * 帮助选项
     */
    @Parameter(names = {"--help", "-h"}, help = true, description = "Show the help information.")
    private boolean help = false;

    /**
     * 获取原路径
     *
     * @return 原路径
     */
    public String getSource() {
        return source;
    }

    /**
     * 获取顶层类型
     *
     * @return 顶层类型
     */
    public TopModelType getType() {
        return TopModelType.loadFromOriginalString(type);
    }

    /**
     * 是否为帮助
     *
     * @return 是否为帮助
     */
    public boolean isHelp() {
        return help;
    }

    /**
     * 获取命令名称
     *
     * @return 命令名称
     */
    @Override
    public String getCommandName() {
        return "list";
    }

    /**
     * 指令运行
     *
     * @throws Exception 异常
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
        } else {
            return ProcessType.LIST;
        }
    }

    /**
     * 帮助信息
     */
    private void processHelp() {
        new JCommander(this).usage();
    }

    /**
     * 列表信息
     *
     * @throws Exception 异常
     */
    private void processList() throws Exception {
        InputWithJson<StarumlFileTopModels, JsonLoadException> loader
                = StarumlFileTopModels::newInstance;
        StarumlFileTopModels models = loader.loadFromFile(getSource());

        List<StarumlFileTopModels.ModelKey> modelKeyList = new ArrayList<>();
        int maxTypeLength = TYPE_TITLE.length();
        int maxNameLength = NAME_TITLE.length();
        for (StarumlFileTopModels.ModelKey key : models.getModelKeySet()) {
            if (getType() == null || getType() == key.getFirstValue()) {
                modelKeyList.add(key);
                maxTypeLength = Math.max(maxTypeLength, key.getFirstValue().getOriginalString().length());
                maxNameLength = Math.max(maxNameLength, key.getSecondValue().length());
            }
        }
        maxNameLength += 2;
        maxTypeLength += 2;

        System.out.println(String.format("| %s | %s |",
                StringUtils.fillWhiteSpaceAlignMiddle(NAME_TITLE, maxNameLength),
                StringUtils.fillWhiteSpaceAlignMiddle(TYPE_TITLE, maxTypeLength)
        ));
        System.out.println(String.format("|%s|%s|",
                StringUtils.repeatString("-", maxNameLength + 2),
                StringUtils.repeatString("-", maxTypeLength + 2)
        ));
        for (StarumlFileTopModels.ModelKey key : modelKeyList) {
            System.out.println(String.format("| %s | %s |",
                    StringUtils.fillWhiteSpaceAlignLeft(key.getSecondValue(), maxNameLength),
                    StringUtils.fillWhiteSpaceAlignLeft(key.getFirstValue().getOriginalString(), maxTypeLength)
            ));
        }
    }

    /**
     * 处理类型
     */
    private enum ProcessType {
        HELP,
        LIST,
    }
}
