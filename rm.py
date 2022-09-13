import os
import shutil

for dirpath, dirnames, filenames in os.walk('.'):
    for dirname in dirnames:
        if dirname == ".git":
            os.rename(os.path.join(dirpath, dirname), os.path.join(dirpath, "_git"))

