from pprint import pprint
import sys

from . import deserialize_what4_from_file
from .visitors.what4_deserialize_backends import Z3Backend


if __name__ == '__main__':
    backend = Z3Backend()
    deserialized = deserialize_what4_from_file(sys.argv[1], backend)
    print(deserialized)
