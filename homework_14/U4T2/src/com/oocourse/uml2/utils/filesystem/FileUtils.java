package com.oocourse.uml2.utils.filesystem;

import java.io.File;

public class FileUtils {
    /**
     * 判断是否为文件
     *
     * @param filename 文件
     * @return 是否为文件
     */
    public static boolean isFile(String filename) {
        return new File(filename).isFile();
    }

    /**
     * 判断文件是否存在
     *
     * @param filename 文件
     * @return 文件是否存在
     */
    public static boolean isFileExists(String filename) {
        return new File(filename).exists();
    }

    /**
     * 判断文件是否可以读取
     *
     * @param filename 文件
     * @return 文件是否可以读取
     */
    public static boolean isFileCanRead(String filename) {
        if (isFileExists(filename)) {
            return new File(filename).canRead();
        } else {
            return false;
        }
    }
}
