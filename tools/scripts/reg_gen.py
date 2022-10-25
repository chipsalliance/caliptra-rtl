# SPDX-License-Identifier: Apache-2.0
# Copyright 2022 Microsoft Corporation or its affiliates.
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
from math import log, ceil
import sys
import os

#output directory for dumping files
rtl_output_dir = os.path.abspath(os.path.dirname(sys.argv[1]))

# Listener to retrieve the address width at the CPU IF and write as a param to the pkg
class SVPkgAppendingListener(RDLListener):

    def __init__(self, file_path):
        self.file_path = file_path
        self.orig_file = ""

    def enter_Addrmap(self,node):
        pkg_file_path = os.path.join(self.file_path, node.inst_name + "_pkg.sv")
        self.file = open(pkg_file_path, 'r')
        for line in self.file.readlines():
            if (line != "endpackage"):
                self.orig_file += line
        self.file.close()
        self.file = open(pkg_file_path, 'w')
        self.file.write(self.orig_file)
        self.file.write("\n    localparam " + node.inst_name.upper() + "_ADDR_WIDTH = " + "32'd" + str(int(ceil(log(node.total_size, 2)))) + ";")

    def exit_Addrmap(self, node):
        self.file.write("\n\nendpackage")
        self.file.close()

# Create an instance of the compiler
rdlc = RDLCompiler()
try:
    # Compile your RDL files
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

except RDLCompileError:
    # A compilation error occurred. Exit with error code
    sys.exit(1)
