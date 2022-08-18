package com.oocourse.uml2.args.commands;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.oocourse.uml2.args.exceptions.CommandLineProcessException;
import com.oocourse.uml2.args.validations.FileAccessibleValidation;
import com.oocourse.uml2.args.validations.TopModelTypeValidation;
import com.oocourse.uml2.models.elements.UmlElement;
import com.oocourse.uml2.models.exceptions.UmlParseException;
import com.oocourse.uml2.models.top.StarumlFileTopModels;
import com.oocourse.uml2.models.top.StarumlModelWalker;
import com.oocourse.uml2.models.top.TopModelType;
import com.oocourse.uml2.utils.common.RunnableWithException;
import com.oocourse.uml2.utils.json.InputWithJson;
import com.oocourse.uml2.utils.json.JsonLoadException;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * dump命令解析
 */
@SuppressWarnings({"FieldCanBeLocal", "WeakerAccess"})
public class DumpCommand extends AbstractCommand {
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
    @Parameter(names = {"--type", "-t"}, description = "Type of the source data.",
            validateWith = TopModelTypeValidation.class, required = true)
    private String type;
    /**
     * 查询名称
     */
    @Parameter(names = {"--name", "-n"}, description = "Name of the source data.", required = true)
    private String name;
    private final Map<ProcessType, RunnableWithException> PROCESSES
            = Collections.unmodifiableMap(new HashMap<ProcessType, RunnableWithException>() {{
        put(ProcessType.HELP, DumpCommand.this::processHelp);
        put(ProcessType.DUMP, DumpCommand.this::processDump);
    }});
    /**
     * 帮助选项
     */
    @Parameter(names = {"--help", "-h"}, help = true, description = "Show the help information.")
    private boolean help = false;

    /**
     * 获取根路径
     *
     * @return 根路径
     */
    public String getSource() {
        return source;
    }

    /**
     * 获取类型
     *
     * @return 类型
     */
    public TopModelType getType() {
        return TopModelType.loadFromOriginalString(type);
    }

    /**
     * 获取名称
     *
     * @return 名称
     */
    public String getName() {
        return name;
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
     * 获取指令名称
     *
     * @return 指令名称
     */
    @Override
    public String getCommandName() {
        return "dump";
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
            return ProcessType.DUMP;
        }
    }

    /**
     * 帮助信息
     */
    private void processHelp() {
        new JCommander(this).usage();
    }

    /**
     * 数据导出
     *
     * @throws Exception 异常信息
     */
    private void processDump() throws Exception {
        InputWithJson<StarumlFileTopModels, JsonLoadException> loader
                = StarumlFileTopModels::newInstance;
        StarumlFileTopModels models = loader.loadFromFile(getSource());
        if (models.containsModel(getType(), getName())) {
            Object jsonObject = models.getModel(getType(), getName());
            StarumlModelWalker walker = new StarumlModelWalker(jsonObject) {
                @Override
                public void umlElementEvent(UmlElement element) {
                    System.out.println(element.toJsonString());
                }

                @Override
                public void parseErrorEvent(UmlParseException exception) {
                    // do nothing
                }
            };
            walker.walk();
        } else {
            throw new CommandLineProcessException(-1, String.format("Model \"%s\" (type %s) not found",
                    getName(), getType().getOriginalString()));
        }
    }

    /**
     * 处理类型
     */
    private enum ProcessType {
        HELP,
        DUMP,
    }
}
