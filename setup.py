from setuptools import setup, Extension
from setuptools.command.install import install
import subprocess
import os
'''
class CustomInstall(install):
    def run(self):
        command = "git clone https://mygit.com/myAwesomeCLibrary.git"
        process = subprocess.Popen(command, shell=True, cwd="packageName")
        process.wait()
        install.run(self)
'''

C_utils = Extension("FloTest.testlib",
                    sources=["src/FloTest/C_utils/testC.c"],
                    extra_compile_args=['-shared','-Wl,-soname,testlib','-fPIC'],
                    extra_link_args =['-ljson-c'],
                    include_dirs=["src/FloTest/include"],
                    language='c'
                    )
def run_setup():
    setup(
        name = 'attack_tree',
        version = '0.1',
        description = 'An example of an installable program',
        author = 'flo',
        url = '',
        license = '',
        package_dir={"": "src"},
        packages=["FloTest"],
        #package_data = {
        #    '': ['*.txt', '*.json', '*.html', '*.csv', '*.conf'],
        #},
        python_requires=">=3",
        #install_requires=[
        #    'matplotlib>=3.4.3',
        #    'networkx>=2.6.3',
        #    'PyQt5>=5.15.6',
        #    'pysat>=3.0.1',
        #    'PySMT>=0.9.0',
        #    'pyvis>=0.1.9',
        #    'setuptools>=52.0.0',
        #    'sympy>=1.9',
        #    'z3>=0.2.0'
        #],
        #cmdclass={'install': CustomInstall},
        #include_package_data=True,
        #scripts=['src/FloTest/ParserWorker.py'],
        ext_modules=[C_utils],
        entry_points={
            "console_scripts": [
                "tree_launcher=FloTest.t:start",
            ],
        },
    )

try:
    run_setup()
except SystemExit as e:
    print(e)