# SPDX-License-Identifier: Apache-2.0
# 
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

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
