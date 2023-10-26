


from setuptools import setup, find_packages
from os import path

NAME = 'wmibench'
DESCRIPTION = 'Unified benchmark library for Weighted Model Integration.'
URL = 'http://github.com/weighted-model-integration/wmibench'
EMAIL = 'paolo.morettin@kuleuven.be'
AUTHOR = 'Paolo Morettin'
REQUIRES_PYTHON = '>=3.5.0'
VERSION = "1.0"

# What packages are required for this module to be executed?
REQUIRED = [
    'pysmt', 'pywmi'
]

# What packages are optional?
EXTRAS = {
#        'sdd': ["pysdd"]
}

here = path.abspath(path.dirname(__file__))

with open(path.join(here, "README.md")) as ref:
    long_description = ref.read()


setup(
    name=NAME,
    version=VERSION,
    description=DESCRIPTION,
    long_description=long_description,
    long_description_content_type="text/markdown",
    url=URL,
    author=AUTHOR,
    author_email=EMAIL,
    license='MIT',
    classifiers=[
        'License :: OSI Approved :: MIT License',
        'Programming Language :: Python',
        'Programming Language :: Python :: 3',
    ],
    python_requires=REQUIRES_PYTHON,
    packages=find_packages(),
#    packages=find_packages(exclude=('test', 'examples')),
    zip_safe=False,
    install_requires=REQUIRED,
    extras_require=EXTRAS
)
