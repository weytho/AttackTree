from setuptools import setup, find_packages

setup(
    name = 'attack_tree',
    version = '0.1',
    description = 'An example of an installable program',
    author = 'flo',
    url = '',
    license = '',
    package_dir={"": "src"},
    packages=["FloTest"],
    python_requires=">=3",
    entry_points={
        "console_scripts": [
            "tree_launcher=FloTest.t:start",
        ],
    },
)