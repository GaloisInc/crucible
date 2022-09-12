from setuptools import setup, find_namespace_packages, find_packages

setup(
    name='crucible_memory_model',
    version='0.0.1',
    description='Crucible memory model',
    author='Galois, Inc.',
    packages=find_namespace_packages(include=['crucible_memory_model.*']),
    install_requires=[
        'crucible_protobuf_trace',
        'what4_deserialize',
        'pyrsistent',
        'z3-solver',
        'lark-parser',
        'networkx',
        'pygraphviz',
        'typen',
    ],
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: BSD License",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.6',
)
