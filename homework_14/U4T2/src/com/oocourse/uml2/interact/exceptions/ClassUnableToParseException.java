package com.oocourse.uml2.interact.exceptions;

/**
 * 数据类型无法解析
 * 注意：
 * 1、解析的方式是从该类中获取public static xxx valueOf(String str)方法
 * 2、找不到此方法，就会进行报错
 */
public class ClassUnableToParseException
        extends InputArgumentParseException {
    /**
     * 构造函数
     *
     * @param errorClass 异常数据类型
     */
    public ClassUnableToParseException(
            Class<?> errorClass) {
        super(
                String.format(
                        "%s is not able to parse for" +
                                " it has no method valueOf " +
                                "with public static modifier.",
                        errorClass.getName()
                ),
                errorClass,
                null
        );
    }
}
