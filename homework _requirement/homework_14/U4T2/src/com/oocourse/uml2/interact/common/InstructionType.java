package com.oocourse.uml2.interact.common;

import com.oocourse.uml2.interact.parser.InputArgumentParser;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

public enum InstructionType {
    CLASS_COUNT,
    CLASS_SUBCLASS_COUNT,
    CLASS_OPERATION_COUNT,
    CLASS_OPERATION_VISIBILITY,
    CLASS_OPERATION_COUPLING_DEGREE,
    CLASS_ATTR_COUPLING_DEGREE,
    CLASS_IMPLEMENT_INTERFACE_LIST,
    CLASS_DEPTH_OF_INHERITANCE,

    STATE_COUNT,
    STATE_IS_CRITICAL_POINT,
    TRANSITION_TRIGGER,

    PTCP_OBJ_COUNT,
    PTCP_CREATOR,
    PTCP_LOST_AND_FOUND;

    public static final InputArgumentParser COMMON_PARSER
        = InputArgumentParser.newInstance(new Class<?>[]{InstructionType.class}, String.class);
    public static final Map<InstructionType, InputArgumentParser> INSTRUCTION_PARSERS
            = Collections.unmodifiableMap(new HashMap<InstructionType, InputArgumentParser>() {{
                    put(CLASS_COUNT,
                            InputArgumentParser.newInstance(InstructionType.class));
                    put(CLASS_SUBCLASS_COUNT,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));
                    put(CLASS_OPERATION_COUNT,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));
                    put(CLASS_OPERATION_VISIBILITY,
                            InputArgumentParser.newInstance(InstructionType.class, String.class,
                                    String.class));
                    put(CLASS_OPERATION_COUPLING_DEGREE,
                            InputArgumentParser.newInstance(InstructionType.class, String.class,
                                    String.class));
                    put(CLASS_ATTR_COUPLING_DEGREE,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));
                    put(CLASS_IMPLEMENT_INTERFACE_LIST,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));
                    put(CLASS_DEPTH_OF_INHERITANCE,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));

                    put(STATE_COUNT,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));
                    put(STATE_IS_CRITICAL_POINT,
                            InputArgumentParser.newInstance(InstructionType.class, String.class,
                                    String.class));
                    put(TRANSITION_TRIGGER,
                            InputArgumentParser.newInstance(InstructionType.class, String.class, String.class, String.class));

                    put(PTCP_OBJ_COUNT,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));
                    put(PTCP_CREATOR,
                            InputArgumentParser.newInstance(InstructionType.class, String.class,
                                    String.class));
                    put(PTCP_LOST_AND_FOUND,
                            InputArgumentParser.newInstance(InstructionType.class, String.class,
                                    String.class));
                }}
    );
}
