from setuptools import setup, find_packages, find_namespace_packages

# the antlr files do not contain __init__.py, so we need to manually include that package
pkgs = find_namespace_packages(include=['what4_deserialize.*']) + ['what4_deserialize.antlr']
deps = [
    'antlr4-python3-runtime',
    'z3-solver',
]

setup(
    name='what4_deserialize',
    version='0.0.1',
    packages=pkgs,
    install_requires=deps,
    entry_points={
        'console_scripts': [
            'what4_deserialize = what4_deserialize.__main__:main',
        ],
    },
)