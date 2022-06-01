from setuptools import setup, Extension

C_utils = Extension("at_magi.testlib",
                    sources=["src/at_magi/C_utils/testC.c"],
                    extra_compile_args=['-shared','-Wl,-soname,testlib','-fPIC'],
                    extra_link_args =['-ljson-c'],
                    include_dirs=["src/at_magi/include"],
                    language='c'
                    )
def run_setup():
    setup(
        name = 'AttackTree_MAGI',
        version = '0.1',
        description = 'Attack Tree Modelling and Analysis Graphical Interface',
        author = 'Delcourt F. and Weiser T.',
        url = '',
        license = '',
        package_dir={"": "src"},
        packages=["at_magi"],
        package_data = {
            '': ['resources_directory.txt'],
        },
        python_requires=">=3.8",
        ext_modules=[C_utils],
        entry_points={
            "console_scripts": [
                "atmagi_launcher=at_magi.t:start",
            ],
        },
    )

try:
    run_setup()
except SystemExit as e:
    print(e)
