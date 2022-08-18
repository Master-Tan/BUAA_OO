package com.oocourse.uml2.utils.string;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.BiFunction;

/**
 * 字符串对齐
 */
@SuppressWarnings({"unused", "WeakerAccess"})
public class AlignedString {
    private static final Integer NO_MIN_LENGTH = null;
    private static final Integer NO_MAX_LENGTH = null;
    private static final String DEFAULT_OMISSION = StringUtils.DEFAULT_OMISSION;
    private static final AlignMode DEFAULT_ALIGN_MODE = AlignMode.DEFAULT;
    private final Object content;
    private final Integer minLength;
    private final Integer maxLength;
    private final String omission;
    private final AlignMode alignMode;

    /**
     * 构造函数
     *
     * @param content   对象
     * @param minLength 最小长度
     * @param maxLength 最大长度
     * @param omission  省略符
     * @param alignMode 对齐方式
     */
    private AlignedString(Object content, Integer minLength, Integer maxLength, String omission, AlignMode alignMode) {
        this.content = content;
        this.minLength = minLength;
        this.maxLength = maxLength;
        this.omission = omission;
        this.alignMode = alignMode;
    }

    /**
     * 获取对齐对象
     *
     * @param content 原对象
     * @return 对齐对象
     */
    public static AlignedString getAlignedString(Object content) {
        return getAlignedString(content, NO_MIN_LENGTH);
    }

    /**
     * 获取对齐对象
     *
     * @param content   原对象
     * @param minLength 最小长度
     * @return 对齐对象
     */
    public static AlignedString getAlignedString(Object content, Integer minLength) {
        return getAlignedString(content, minLength, DEFAULT_ALIGN_MODE);
    }

    /**
     * 获取对齐对象
     *
     * @param content   原对象
     * @param minLength 最小长度
     * @param alignMode 对其模式
     * @return 对齐对象
     */
    public static AlignedString getAlignedString(Object content, Integer minLength, AlignMode alignMode) {
        return new AlignedString(
                content,
                minLength,
                NO_MAX_LENGTH,
                DEFAULT_OMISSION,
                alignMode
        );
    }

    /**
     * 获取对齐对象
     *
     * @param content   原对象
     * @param maxLength 最大长度
     * @return 对齐对象
     */
    public static AlignedString getTruncatedString(Object content, Integer maxLength) {
        return getTruncatedString(content, maxLength, DEFAULT_OMISSION);
    }

    /**
     * 获取对齐对象
     *
     * @param content   原对象
     * @param maxLength 最大长度
     * @param omission  省略符
     * @return 对齐对象
     */
    public static AlignedString getTruncatedString(Object content, Integer maxLength, String omission) {
        return new AlignedString(
                content,
                NO_MIN_LENGTH,
                maxLength,
                omission,
                DEFAULT_ALIGN_MODE
        );
    }

    /**
     * 获取对象
     *
     * @return 对象
     */
    public Object getContent() {
        return content;
    }

    /**
     * 获取最小长度
     *
     * @return 最小长度
     */
    public Integer getMinLength() {
        return minLength;
    }

    /**
     * 是否有最小长度
     *
     * @return 是否有最小长度
     */
    public boolean hasMinLength() {
        return getMinLength() != null;
    }

    /**
     * 获取最大长度
     *
     * @return 最大长度
     */
    public Integer getMaxLength() {
        return maxLength;
    }

    /**
     * 是否有最大长度
     *
     * @return 是否有最大长度
     */
    public boolean hasMaxLength() {
        return getMaxLength() != null;
    }

    /**
     * 获取省略符
     *
     * @return 省略符
     */
    public String getOmission() {
        return omission;
    }

    /**
     * 获取对齐模式
     *
     * @return 对齐模式
     */
    public AlignMode getAlignMode() {
        return alignMode;
    }

    /**
     * 相等性判断
     *
     * @param o 对象
     * @return 是否相等
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        AlignedString that = (AlignedString) o;
        return Objects.equals(content, that.content) &&
                Objects.equals(minLength, that.minLength) &&
                Objects.equals(maxLength, that.maxLength) &&
                Objects.equals(omission, that.omission) &&
                alignMode == that.alignMode;
    }

    /**
     * 获取哈希值
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(content, minLength, maxLength, omission, alignMode);
    }

    /**
     * 获取原始内容
     *
     * @return 原始内容
     */
    private String getOriginalContent() {
        return String.valueOf(this.content);
    }

    /**
     * 获取显示内容
     *
     * @return 显示内容
     */
    private String getDisplayContent() {
        String alignedString = !hasMinLength() ? this.getOriginalContent()
                : this.alignMode.align(getOriginalContent(), minLength);
        return !hasMaxLength() ? alignedString
                : StringUtils.truncate(alignedString, maxLength, omission);
    }

    /**
     * 获取字符串形式
     *
     * @return 字符串形式
     */
    public String toString() {
        return getDisplayContent();
    }

    /**
     * 对齐模式
     */
    public enum AlignMode {
        LEFT,
        RIGHT,
        MIDDLE;
        private static final int ZERO_LENGTH = 0;
        private static final String WHITE_SPACE = " ";
        private static final Map<AlignMode, BiFunction<String, Integer, String>> ALIGN_FUNCTIONS
                = Collections.unmodifiableMap(new HashMap<AlignMode, BiFunction<String, Integer, String>>() {{
            put(LEFT, AlignMode::leftAlign);
            put(RIGHT, AlignMode::rightAlign);
            put(MIDDLE, AlignMode::middleAlign);
        }});
        static AlignMode DEFAULT = LEFT;

        /**
         * 左对齐
         *
         * @param originalString 原字符串
         * @param length         对齐长度
         * @return 对齐结果
         */
        private static String leftAlign(String originalString, Integer length) {
            int remainLength = Math.max(length - originalString.length(), ZERO_LENGTH);
            StringBuilder builder = new StringBuilder();
            builder.append(originalString);
            StringProcessUtils.appendRepeatedWords(builder, WHITE_SPACE, remainLength);
            return builder.toString();
        }

        /**
         * 右对齐
         *
         * @param originalString 原字符串
         * @param length         对其长度
         * @return 对齐结果
         */
        private static String rightAlign(String originalString, Integer length) {
            int remainLength = Math.max(length - originalString.length(), ZERO_LENGTH);
            StringBuilder builder = new StringBuilder();
            StringProcessUtils.appendRepeatedWords(builder, WHITE_SPACE, remainLength);
            builder.append(originalString);
            return builder.toString();
        }

        /**
         * 居中对齐
         *
         * @param originalString 原字符串
         * @param length         对齐长度
         * @return 对齐结果
         */
        private static String middleAlign(String originalString, Integer length) {
            int remainLength = Math.max(length - originalString.length(), ZERO_LENGTH);
            int leftLength = remainLength / 2;
            int rightLength = remainLength - leftLength;
            StringBuilder builder = new StringBuilder();
            StringProcessUtils.appendRepeatedWords(builder, WHITE_SPACE, leftLength);
            builder.append(originalString);
            StringProcessUtils.appendRepeatedWords(builder, WHITE_SPACE, rightLength);
            return builder.toString();
        }

        /**
         * 对齐操作
         *
         * @param originalString 原字符串
         * @param length         对齐长度
         * @return 对齐结果
         */
        public String align(String originalString, Integer length) {
            return ALIGN_FUNCTIONS.get(this).apply(originalString, length);
        }
    }
}
