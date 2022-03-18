# Copyright (C) Microsoft Corporation. All rights reserved.

# Simple script to parse INI and make shell variables from it
import sys
from configparser import ConfigParser, ExtendedInterpolation

config = ConfigParser(interpolation=ExtendedInterpolation())
config.read_file(sys.stdin)

for sec in config.sections():
    print("declare -A %s" % (sec))
    for key, val in config.items(sec):
        print('%s[%s]="%s"' % (sec, key, val))
