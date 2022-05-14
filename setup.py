from setuptools import setup, Extension

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
        package_data = {
            '': ['resources_directory.txt'],
        },
        python_requires=">=3.8",
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
