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
import com.oocourse.uml2.utils.string.AlignedString;
import com.oocourse.uml2.utils.string.DynamicString;
import com.oocourse.uml2.utils.string.table.Table;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * 列表命令解析
 */
@SuppressWarnings({"FieldCanBeLocal", "WeakerAccess"})
public class ListCommand extends AbstractCommand {
    private static final String TYPE_TITLE = "Type";
    private static final String NAME_TITLE = "Name";
    private static final String ID_TITLE = "ID";
    private static final String PARENT_ID_TITLE = "Parent Id";
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
            validateWith = TopModelTypeValidation.class)
    private String type = null;
    /**
     * 查询的模型名称
     */
    @Parameter(names = {"--name", "-n"}, description = "Name of the model.")
    private String modelName;
    private final Map<ProcessType, RunnableWithException> PROCESSES
            = Collections.unmodifiableMap(new HashMap<ProcessType, RunnableWithException>() {{
        put(ProcessType.HELP, ListCommand.this::processHelp);
        put(ProcessType.MODEL_LIST, ListCommand.this::processModelList);
        put(ProcessType.MODEL_ELEMENT_LIST, ListCommand.this::processModelElementList);
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
     * 获取待查询的模型名称
     *
     * @return 模型名称
     */
    public String getModelName() {
        return modelName;
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
        } else if (getModelName() != null) {
            return ProcessType.MODEL_ELEMENT_LIST;
        } else {
            return ProcessType.MODEL_LIST;
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
    private void processModelList() throws Exception {
        InputWithJson<StarumlFileTopModels, JsonLoadException> loader
                = StarumlFileTopModels::newInstance;
        StarumlFileTopModels models = loader.loadFromFile(getSource());

        Table table = new Table(
                AlignedString.getAlignedString(TYPE_TITLE, TYPE_TITLE.length() + 2, AlignedString.AlignMode.MIDDLE),
                AlignedString.getAlignedString(NAME_TITLE, NAME_TITLE.length() + 2, AlignedString.AlignMode.MIDDLE)
        );

        for (StarumlFileTopModels.ModelKey key : models.getModelKeySet()) {
            if (getType() == null || getType() == key.getFirstValue()) {
                table.addRow(
                        new DynamicString<>(key, modelKey -> modelKey.getFirstValue().getOriginalString()),
                        new DynamicString<>(key, StarumlFileTopModels.ModelKey::getSecondValue)
                );
            }
        }
        System.out.println(table);
    }

    /**
     * 元素列表信息
     *
     * @throws Exception 异常
     */
    private void processModelElementList() throws Exception {
        InputWithJson<StarumlFileTopModels, JsonLoadException> loader
                = StarumlFileTopModels::newInstance;
        StarumlFileTopModels models = loader.loadFromFile(getSource());
        if (models.containsModel(getType(), getModelName())) {
            Object jsonObject = models.getModel(getType(), getModelName());
            Table table = new Table(
                    AlignedString.getAlignedString(TYPE_TITLE, TYPE_TITLE.length() + 2, AlignedString.AlignMode.MIDDLE),
                    AlignedString.getAlignedString(NAME_TITLE, NAME_TITLE.length() + 2, AlignedString.AlignMode.MIDDLE),
                    AlignedString.getAlignedString(ID_TITLE, ID_TITLE.length() + 2, AlignedString.AlignMode.MIDDLE),
                    AlignedString.getAlignedString(PARENT_ID_TITLE, PARENT_ID_TITLE.length() + 2, AlignedString.AlignMode.MIDDLE)
            );

            StarumlModelWalker walker = new StarumlModelWalker(jsonObject) {
                @Override
                public void umlElementEvent(UmlElement element) {
                    table.addRow(
                            new DynamicString<>(element, umlElement -> umlElement.getElementType().getOriginalString()),
                            new DynamicString<>(element, UmlElement::getName),
                            new DynamicString<>(element, UmlElement::getId),
                            new DynamicString<>(element, UmlElement::getParentId)
                    );
                }

                @Override
                public void parseErrorEvent(UmlParseException exception) {
                    // do nothing
                }
            };
            walker.walk();
            System.out.println(table);
        } else {
            throw new CommandLineProcessException(-1, String.format("Model \"%s\" (type %s) not found",
                    getModelName(), getType().getOriginalString()));
        }
    }

    /**
     * 处理类型
     */
    private enum ProcessType {
        HELP,
        MODEL_LIST,
        MODEL_ELEMENT_LIST
    }
}
