# AttackTree

# Doxygen
doxygen -g settings/attacktree.conf
doxygen settings/attacktree.conf

# then make in the latex folder

# Install & Run

# With Installer
> sh install.sh
> atmagi_launcher

# Manual usage
> gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC UtilsC.c -ljson-c
> python ATMAGI.py