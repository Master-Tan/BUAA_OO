package com.oocourse.uml2.interact;


/**
 * 输出加密模块
 */
class OutputEncryption {
    /**
     * 原字符串
     */
    private final String message;

    /**
     * 构造函数
     *
     * @param message 原字符串
     */
    OutputEncryption(String message) {
        this.message = message;
    }

    /**
     * 构造函数
     *
     * @param message 原字符串
     * @return 加密后的字符串
     */
    static String getEncryptedMessage(String message) {
        return new OutputEncryption(message).getEncrypted();
    }

    /**
     * 获取原字符串
     *
     * @return 原字符串
     */
    String getMessage() {
        return message;
    }

    /**
     * 获取加密后的字符串
     *
     * @return 加密后的字符串
     */
    String getEncrypted() {
        return message;
    }
}

