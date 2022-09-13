package com.oocourse.uml1.interact.common;

import com.oocourse.uml1.interact.parser.InputArgumentParser;

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
    CLASS_DEPTH_OF_INHERITANCE;

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
                            InputArgumentParser.newInstance(InstructionType.class, String.class, String.class));
                    put(CLASS_OPERATION_COUPLING_DEGREE,
                            InputArgumentParser.newInstance(InstructionType.class, String.class, String.class));
                    put(CLASS_ATTR_COUPLING_DEGREE,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));
                    put(CLASS_IMPLEMENT_INTERFACE_LIST,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));
                    put(CLASS_DEPTH_OF_INHERITANCE,
                            InputArgumentParser.newInstance(InstructionType.class, String.class));
                }}
            );
}
