# AttackTree

# Doxygen
doxygen -g settings/attacktree.conf
doxygen settings/attacktree.conf

# then make in the latex folder

# Install & Run

sudo apt install libjson-c-dev

gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testC.c -ljson-c
/bin/python3 /home/flo/Desktop/Github/AttackTree/t.py
/bin/python3 /home/thomas/UCL/AttackTree/FloTest/t.py

# https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library

# https://stackoverflow.com/questions/44726280/include-matplotlib-in-pyqt5-with-hover-labels
# https://networkx.org/documentation/stable/reference/classes/digraph.html
# https://stackoverflow.com/questions/56424297/how-to-draw-a-digraph-in-a-org-chart-fashion
# https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library

# https://networkx.org/documentation/stable/_modules/networkx/drawing/nx_agraph.html#pygraphviz_layout
# https://visjs.github.io/vis-network/docs/network/nodes.html



# For requirements :
pip install -r requirements.txt

python setup.py sdist

pip install --upgrade urllib3
pipreqs

pip install -r requirements.txt

sudo python3 setup.py clean --all

pip install . --versbose

tree_launch

pyinstaller --onefile hello.py