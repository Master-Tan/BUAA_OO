package com.oocourse.uml1.args.validations;

import com.beust.jcommander.IParameterValidator;
import com.beust.jcommander.ParameterException;
import com.oocourse.uml1.utils.filesystem.FileUtils;

public class FileAccessibleValidation implements IParameterValidator {
    @Override
    public void validate(String name, String value) throws ParameterException {
        if (!FileUtils.isFile(value)) {
            throw new ParameterException(String.format("\"%s\" is not a file.", value));
        } else if (!FileUtils.isFileExists(value)) {
            throw new ParameterException(String.format("File \"%s\" not found.", value));
        } else if (!FileUtils.isFileCanRead(value)) {
            throw new ParameterException(String.format("File \"%s\" not accessible.", value));
        }
    }
}
