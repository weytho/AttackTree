# AttackTree

# Doxygen
doxygen -g settings/attacktree.conf
doxygen settings/attacktree.conf

# then make in the latex folder

# Install & Run

# With Installer
> sh install.sh
> tree_launcher

# Manual usage
> gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testC.c -ljson-c
> python t.py