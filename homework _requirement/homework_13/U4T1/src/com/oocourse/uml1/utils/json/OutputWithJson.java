package com.oocourse.uml1.utils.json;

import org.json.simple.JSONValue;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;

/**
 * JSON输出接口
 */
public interface OutputWithJson<T> {
    /**
     * 导出到文件
     *
     * @param filename 文件名
     * @throws IOException 读写异常
     */
    default void dumpToFile(String filename) throws IOException {
        dumpToFile(new File(filename));
    }

    /**
     * 导出到文件
     *
     * @param file 文件对象
     * @throws IOException 读写异常
     */
    default void dumpToFile(File file) throws IOException {
        FileWriter writer = new FileWriter(file);
        JSONValue.writeJSONString(toJson(), writer);
        writer.close();
    }

    /**
     * 导出到输出流
     *
     * @param outputStream 输出流
     * @param charsetName  字符集名称
     * @throws IOException 读写异常
     */
    default void dumpToStream(OutputStream outputStream, String charsetName) throws IOException {
        OutputStreamWriter writer = new OutputStreamWriter(outputStream, charsetName);
        JSONValue.writeJSONString(toJson(), writer);
        writer.close();
    }

    /**
     * 导出到输出流
     *
     * @param outputStream 输出流
     * @throws IOException 读写异常
     */
    default void dumpToStream(OutputStream outputStream) throws IOException {
        dumpToStream(outputStream, null);
    }

    /**
     * 转为JSON字符串
     *
     * @return JSON字符串
     */
    default String toJsonString() {
        return JSONValue.toJSONString(toJson());
    }

    /**
     * 导出JSON数据
     *
     * @return JSON数据
     */
    T toJson();
}
