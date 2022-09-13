class PathNotFoundException extends Exception {
    PathNotFoundException(final Path path) {
        if (path != null) {
            System.err.println(path.toString() + " Not Found!");
        } else {
            System.err.println("NullPointer");
        }

    }
}