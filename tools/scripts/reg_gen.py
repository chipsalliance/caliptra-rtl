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
# This script generates systemverilog registers from rdl files
# Currently, this script uses peakrdl-regblock version 0.6.0
#
#   pip install peakrdl-regblock==0.6.0
# 
# TODO: To update this script to the latest version (0.11.0)
# 1.  Import ALL_UDPS
#     from peakrdl_regblock.udps import ALL_UDPS
# 2.  Register ALL_UDPS after creating instance of compiler
#     rdlc = RDLCompiler()
#
#     Register all UDPs that 'regblock' requires
#     for udp in ALL_UDPS:
#       rdlc.register_udp(udp)

from systemrdl import RDLCompiler, RDLCompileError, RDLWalker
from systemrdl import RDLListener
from systemrdl.node import FieldNode
from peakrdl_regblock import RegblockExporter
from peakrdl_uvm import UVMExporter
from peakrdl_html import HTMLExporter
from peakrdl_regblock.udps import ALL_UDPS
from peakrdl_regblock.cpuif.passthrough import PassthroughCpuif
from math import log, ceil, floor
import sys
import os
import re
import rdl_post_process

#output directory for dumping files
rtl_output_dir = os.path.abspath(os.path.dirname(sys.argv[1]))
repo_root = os.environ.get('CALIPTRA_ROOT')

# Listener to retrieve the address width at the CPU IF and write as a param to the pkg
class SVPkgAppendingListener(RDLListener):

    def __init__(self, file_path):
        self.file_path = file_path
        self.orig_file = ""

    def enter_Addrmap(self,node):
        self.regfile_name = os.path.join(self.file_path, node.inst_name)
        pkg_file_path = str(self.regfile_name + "_pkg.sv")
        self.file = open(pkg_file_path, 'r')
        for line in self.file.readlines():
            if (re.search(r'\bendpackage\b', line) is None):
                self.orig_file += line
        self.file.close()
        self.file = open(pkg_file_path, 'w')
        self.file.write(self.orig_file)
        self.file.write("\n    localparam " + node.inst_name.upper() + "_ADDR_WIDTH = " + "32'd" + str(int(floor(log(node.total_size, 2)) + 1)) + ";")

    def exit_Addrmap(self, node):
        self.file.write("\n\nendpackage")
        self.file.close()

    def get_regfile_name(self):
        return self.regfile_name

# Create an instance of the compiler
rdlc = RDLCompiler()

# Register all UDPs that 'regblock' requires
for udp in ALL_UDPS:
    rdlc.register_udp(udp)

try:
    if not repo_root:
      print("CALIPTRA_ROOT environment variable is not defined.")
    # Compile your RDL files
    #compile the kv defines so that rdl files including kv controls have the definition
    rdlc.compile_file(os.path.join(repo_root, "src/keyvault/rtl/kv_def.rdl")) 
    rdlc.compile_file(sys.argv[1])

    # Elaborate the design
    root = rdlc.elaborate()

    # Export a SystemVerilog implementation
    exporter = RegblockExporter()
    exporter.export(
        root, rtl_output_dir,
        cpuif_cls=PassthroughCpuif,
        retime_read_response=False
    )

    # Export a UVM register model
    exporter = UVMExporter(user_template_dir=os.path.join(repo_root, "tools/templates/rdl/uvm"))
    exporter.export(root, os.path.join(rtl_output_dir, os.path.splitext(os.path.basename(sys.argv[1]))[0]) + "_uvm.sv")
    # The below lines are used to generate a baseline/starting point for the include files "<reg_name>_covergroups.svh" and "<reg_name>_sample.svh"
    # The generated files will need to be hand-edited to provide the desired functionality.
    # Uncomment these lines and run this script directly on the target RDL file to generate the files.
#    exporter = UVMExporter(user_template_dir=os.path.join(repo_root, "tools/templates/rdl/cov"))
#    exporter.export(root, os.path.join(rtl_output_dir, os.path.splitext(os.path.basename(sys.argv[1]))[0]) + "_covergroups.svh")
#    exporter = UVMExporter(user_template_dir=os.path.join(repo_root, "tools/templates/rdl/smp"))
#    exporter.export(root, os.path.join(rtl_output_dir, os.path.splitext(os.path.basename(sys.argv[1]))[0]) + "_sample.svh")

    # Traverse the register model!
    walker = RDLWalker(unroll=True)
    pkglistener = SVPkgAppendingListener(rtl_output_dir)
    walker.walk(root, pkglistener)

    # Scrub the output SystemVerilog files to modify the coding style
    #  - Change unpacked arrays to packed, unpacked structs to packed
    # TODO just make a new exporter template instead of scrubbing?
    rdl_post_process.scrub_line_by_line(str(pkglistener.get_regfile_name() + ".sv"))
    rdl_post_process.scrub_line_by_line(str(pkglistener.get_regfile_name() + "_pkg.sv"))

except RDLCompileError:
    # A compilation error occurred. Exit with error code
    sys.exit(1)
