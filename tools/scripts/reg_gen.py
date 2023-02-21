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
from systemrdl import RDLCompiler, RDLCompileError, RDLWalker
from systemrdl import RDLListener
from systemrdl.node import FieldNode
from peakrdl_regblock import RegblockExporter
from peakrdl_uvm import UVMExporter
from peakrdl_html import HTMLExporter
from peakrdl_regblock.cpuif.passthrough import PassthroughCpuif
from math import log, ceil, floor
import sys
import os
import rdl_post_process

#output directory for dumping files
rtl_output_dir = os.path.abspath(os.path.dirname(sys.argv[1]))
workspace = os.environ.get('WORKSPACE')

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
            if (line != "endpackage"):
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
try:
    # Compile your RDL files
    #compile the kv defines so that rdl files including kv controls have the definition
    rdlc.compile_file(workspace + "/Caliptra/src/keyvault/rtl/kv_def.rdl") 
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
    exporter = UVMExporter()
    exporter.export(root, os.path.join(rtl_output_dir, os.path.splitext(os.path.basename(sys.argv[1]))[0]) + "_uvm.sv")

    # Traverse the register model!
    walker = RDLWalker(unroll=True)
    pkglistener = SVPkgAppendingListener(rtl_output_dir)
    walker.walk(root, pkglistener)

    # Scrub the output SystemVerilog files to modify the coding style
    #  - Change unpacked arrays to packed, unpacked structs to packed
    rdl_post_process.scrub_line_by_line(str(pkglistener.get_regfile_name() + ".sv"))
    rdl_post_process.scrub_line_by_line(str(pkglistener.get_regfile_name() + "_pkg.sv"))

except RDLCompileError:
    # A compilation error occurred. Exit with error code
    sys.exit(1)
