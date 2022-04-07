from setuptools import setup
from setuptools import find_namespace_packages

setup(

    name="Attack tree tool",
    author="Delfourt Florentin & Weiser Thomas",
    version='1.0.0',
    description="Student thesis creating a tool to compute theoretical attack trees",
    url='https://github.com/weytho/AttackTree',
    packages=find_namespace_packages(
        where=['FloTest', 'FloTest.*']
    )
    
)