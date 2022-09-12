#! /usr/bin/env python
#
# See README for usage instructions.

# pylint:disable=missing-module-docstring
# pylint:disable=g-bad-import-order
from distutils import util
import fnmatch
import glob
import os
import shutil
import pkg_resources
import re
import subprocess
import sys
import sysconfig

# pylint:disable=g-importing-member
# pylint:disable=g-multiple-import

# We must use setuptools, not distutils, because we need to use the
# namespace_packages option for the "google" package.
from setuptools import setup, Extension, find_packages, find_namespace_packages

from distutils.command.build_ext import build_ext as _build_ext
from distutils.command.build_py import build_py as _build_py
from distutils.command.clean import clean as _clean
from distutils.spawn import find_executable

# Find the Protocol Compiler.
if 'PROTOC' in os.environ and os.path.exists(os.environ['PROTOC']):
  protoc = os.environ['PROTOC']
elif os.path.exists('../src/protoc'):
  protoc = '../src/protoc'
elif os.path.exists('../src/protoc.exe'):
  protoc = '../src/protoc.exe'
elif os.path.exists('../vsprojects/Debug/protoc.exe'):
  protoc = '../vsprojects/Debug/protoc.exe'
elif os.path.exists('../vsprojects/Release/protoc.exe'):
  protoc = '../vsprojects/Release/protoc.exe'
else:
  protoc = find_executable('protoc')


def GetVersion():
  """Reads and returns the version from google/protobuf/__init__.py.

  Do not import google.protobuf.__init__ directly, because an installed
  protobuf library may be loaded instead.

  Returns:
      The version.
  """

  with open(os.path.join('crucible_protobuf_trace', '__version__.py')) as version_file:
    exec(version_file.read(), globals())  # pylint:disable=exec-used
    return __version__  # pylint:disable=undefined-variable


def GenProto(source, require=True):
  """Generates a _pb2.py from the given .proto file.

  Does nothing if the output already exists and is newer than the input.

  Args:
      source: the .proto file path.
      require: if True, exit immediately when a path is not found.
  """

  if not require and not os.path.exists(source):
    return

  output = source.replace('.proto', '_pb2.py').replace('../../proto/', './')

  if (not os.path.exists(output) or
      (os.path.exists(source) and
       os.path.getmtime(source) > os.path.getmtime(output))):
    print('Generating %s...' % output)

    if not os.path.exists(source):
      sys.stderr.write("Can't find required file: %s\n" % source)
      sys.exit(-1)

    if protoc is None:
      sys.stderr.write(
          'protoc is not installed nor found in ../src.  Please compile it '
          'or install the binary package.\n')
      sys.exit(-1)

    protoc_command = [protoc, '--proto_path', 'crucible_protobuf_trace=../../proto/crucible_protobuf_trace/', '--python_out=./', source]
    if subprocess.call(protoc_command) != 0:
      sys.exit(-1)


class CleanCmd(_clean):
  """Custom clean command for building the protobuf extension."""

  def run(self):
    # Delete generated files in the code tree.
    for (dirpath, dirnames, filenames) in os.walk('.'):
      for dname in dirnames:
        if dname in {'__pycache__', 'build', 'dist'} or dname.endswith('.egg-info'):
          shutil.rmtree(os.path.join(dirpath, dname))

      for filename in filenames:
        filepath = os.path.join(dirpath, filename)
        if (filepath.endswith('_pb2.py') or filepath.endswith('.pyc') or
            filepath.endswith('.so') or filepath.endswith('.o')):
          os.remove(filepath)
    # _clean is an old-style class, so super() doesn't work.
    _clean.run(self)


class BuildPyCmd(_build_py):
  """Custom build_py command for building the protobuf runtime."""

  def run(self):
    # Generate necessary .proto file if it doesn't exist.
    for f in glob.glob('../../proto/crucible_protobuf_trace/*.proto'):
        GenProto(f)

    # _build_py is an old-style class, so super() doesn't work.
    _build_py.run(self)

  def find_package_modules(self, package, package_dir):
    exclude = (
        '*test*',
    )
    modules = _build_py.find_package_modules(self, package, package_dir)
    return [(pkg, mod, fil) for (pkg, mod, fil) in modules
            if not any(fnmatch.fnmatchcase(fil, pat=pat) for pat in exclude)]


class BuildExtCmd(_build_ext):
  """Command class for building the protobuf Python extension."""

  def get_ext_filename(self, ext_name):
    # since python3.5, python extensions' shared libraries use a suffix that
    # corresponds to the value of sysconfig.get_config_var('EXT_SUFFIX') and
    # contains info about the architecture the library targets.  E.g. on x64
    # linux the suffix is ".cpython-XYZ-x86_64-linux-gnu.so" When
    # crosscompiling python wheels, we need to be able to override this
    # suffix so that the resulting file name matches the target architecture
    # and we end up with a well-formed wheel.
    filename = _build_ext.get_ext_filename(self, ext_name)
    orig_ext_suffix = sysconfig.get_config_var('EXT_SUFFIX')
    new_ext_suffix = os.getenv('PROTOCOL_BUFFERS_OVERRIDE_EXT_SUFFIX')
    if new_ext_suffix and filename.endswith(orig_ext_suffix):
      filename = filename[:-len(orig_ext_suffix)] + new_ext_suffix
    return filename


def GetOptionFromArgv(option_str):
  if option_str in sys.argv:
    sys.argv.remove(option_str)
    return True
  return False


def _GetFlagValues(flag_long, flag_short):
  """Searches sys.argv for distutils-style flags and yields values."""

  expect_value = flag_long.endswith('=')
  flag_res = [re.compile(r'--?%s(=(.*))?' %
                         (flag_long[:-1] if expect_value else flag_long))]
  if flag_short:
    flag_res.append(re.compile(r'-%s(.*)?' % (flag_short,)))

  flag_match = None
  for arg in sys.argv:
    # If the last arg was like '-O', check if this is the library we want.
    if flag_match is not None:
      yield arg
      flag_match = None
      continue

    for flag_re in flag_res:
      m = flag_re.match(arg)
      if m is None:
        continue
      if not expect_value:
        yield arg
        continue
      groups = m.groups()
      # Check for matches:
      #   --long-name=foo => ('=foo', 'foo')
      #   -Xfoo => ('foo')
      # N.B.: if the flag is like '--long-name=', then there is a value
      # (the empty string).
      if groups[0] or groups[-1]:
        yield groups[-1]
        continue
      flag_match = m

  return False


def HasStaticLibprotobufOpt():
  """Returns true if there is a --link-objects arg for libprotobuf."""

  lib_re = re.compile(r'(.*[/\\])?(lib)?protobuf([.]pic)?[.](a|lib)')
  for value in _GetFlagValues('link-objects=', 'O'):
    if lib_re.match(value):
      return True
  return False


def HasLibraryDirsOpt():
  """Returns true if there is a --library-dirs arg."""
  return any(_GetFlagValues('library-dirs=', 'L'))


if __name__ == '__main__':
  ext_module_list = []
  warnings_as_errors = '--warnings_as_errors'
  # Keep this list of dependencies in sync with tox.ini.
  install_requires = ['protobuf', 'antlr4-python3-runtime']

  setup(
      name='crucible_protobuf_trace',
      version=GetVersion(),
      description='Protocol Buffers for crucible\'s protobuf trace',
      long_description =
          "This python package contains the protocol buffer definitions for crucible's protobuf trace. This trace can be " +
          "used to track the symbolic of a program and any actions related to symbolic branching, merging, constraining" +
          "and memory operations. We use it to benchmark different memory model implementations.",
      url='https://github.com/GaloisInc/crucible',
      maintainer='Lukas Dresel <ldresel@galois.com>',
      maintainer_email='ldresel@galois.com',
      license='BSD-3-Clause',
      classifiers=[
          'Programming Language :: Python',
          'Programming Language :: Python :: 3',
          'Programming Language :: Python :: 3.7',
          'Programming Language :: Python :: 3.8',
          'Programming Language :: Python :: 3.9',
          'Programming Language :: Python :: 3.10',
      ],
      packages=find_packages(include='crucible_protobuf_trace.*'),
      cmdclass={
          'clean': CleanCmd,
          'build_py': BuildPyCmd,
          'build_ext': BuildExtCmd,
      },
      install_requires=install_requires,
      ext_modules=ext_module_list,
      python_requires='>=3.7',
  )
