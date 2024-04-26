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

import sys
import os
import re

def scrub_line_by_line(fname):

    # Open file
    rhandle = open(fname, "r+")
    mod_cnt = 0
    mod_lines = ""

    found_hard_reset = None

    # Line by line manipulation
    # Look for unpacked arrays (could be struct arrays or signal arrays)
    # Look for unpacked struct types
    # NOTE: Will not detect unpacked arrays where the array identifier
    #       and dimensions are on separate lines
    for line in rhandle:
        has_assign = re.search(r'\bassign\b', line)
        has_reg_strb = re.search(r'\bdecoded_reg_strb\b', line)
        has_unpacked = re.search(r'\[\d+\]', line)
        has_struct = re.search(r'\bstruct\b\s*(?:unpacked)?', line)
        is_endmodule = re.search(r'\bendmodule\b', line)
        has_reset = re.search(r'\bnegedge\b', line)
        has_enum = re.search(r'\btypedef enum\b', line)
        if (has_reset is not None and found_hard_reset is None):
            substring = re.search(r"negedge (\w+.\w+)", line)
            reset_name = substring.group(1)
            # Find the hard reset if it exists
            # hard_reset_b, error_reset_b and cptra_pwrgood are used interchangeably
            found_hard_reset = re.search(r'hard_reset|pwrgood|error_reset',reset_name)
        # Skip lines with logic assignments or references to signals; we
        # only want to scrub signal definitions for unpacked arrays
        if (has_assign is not None or has_reg_strb is not None):
            mod_lines+=line
        elif (has_enum is not None):
            line = re.sub('enum', 'enum logic [31:0]', line)
            mod_lines+=line
            mod_cnt+=1
        elif (has_struct is not None):
            line = re.sub(r'(\bstruct\b)\s*(?:unpacked)?', r'\1 packed', line)
            mod_lines+=line
            mod_cnt+=1
        elif (has_unpacked is not None):
            while(has_unpacked is not None):
                #               whitespace
                #               |    existing dimensions (packed)
                #               |    |              identifier
                #               |    |              |          unpacked dimensions (ignore this iteration)
                #               |___ |____________  |______    |_______    unpacked dimension to modify
                #               |   \|            \ |      \   |       \   |
                line = re.sub(r'(\s*)(\[[\w-]+:0\])*(\s*\w+)\s*(\[\d+\])*\[(\d+)\]', r'\1[\5-1:0]\2\3\4', line)
                has_unpacked = re.search(r'\[\d+\]', line)
            mod_lines+=line
            mod_cnt+=1
        elif (is_endmodule is not None):
            mod_lines+="\n"
            mod_lines+="`CALIPTRA_ASSERT_KNOWN(ERR_HWIF_IN, hwif_in, clk, !" + reset_name + ")\n"
            mod_lines+="\n"
            mod_lines+=line
        else:
            mod_lines+=line
    #print(f"modified {mod_cnt} lines with unpacked arrays in {fname}")

    # Close file for reading, reopen to write modified contents
    rhandle.close()
    whandle = open(fname, "w")
    whandle.write(mod_lines)
    whandle.close()

if __name__ == "__main__":
    # Get filename to scrub from arguments
    if (len(sys.argv) == 1):
        print(f"{os.path.basename(sys.argv[0])} requires an argument to specify target file!")
    else:
        fname = sys.argv[1]
        print(f"file name to modify is {fname}")

    # Convert Unpacked Arrays/structs to Packed
    scrub_line_by_line(fname)
