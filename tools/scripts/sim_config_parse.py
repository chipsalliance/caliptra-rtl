# Copyright (C) Microsoft Corporation. All rights reserved.

# Simple script to parse INI and make shell variables from it
import sys
#from configparser import ConfigParser, ExtendedInterpolation

import yaml
import os

configFile = sys.argv[1]

with open(configFile, "r") as sim_config_yml_file:
    data = yaml.full_load(sim_config_yml_file)
    for sec in data:
        print("declare -A %s" % sec)
        for subsec in data[sec]:
            print('%s[%s]="%s"' % (sec, subsec, data[sec][subsec]))



#config = ConfigParser(interpolation=ExtendedInterpolation())
#config.read_file(sys.stdin)

#for sec in config.sections():
#    print("declare -A %s" % (sec))
#    for key, val in config.items(sec):
#        print('%s[%s]="%s"' % (sec, key, val))
