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
from peakrdl_regblock.cpuif.passthrough import PassthroughCpuif
from math import log, ceil
import sys
import os

#output directory for dumping files
output_dir = os.path.abspath(sys.argv[2])

# Listener block will print register name and address into C Header file
class CHeaderPrintingListener(RDLListener):
    def __init__(self, file_path):
        self.file_path = file_path

    def enter_Addrmap(self, node):
        header_file_path = os.path.join(self.file_path, node.inst_name + ".h")
        self.file = open(header_file_path, 'w')
        self.file.write("// SPDX-License-Identifier: Apache-2.0\n" +
                        "//\n"
                        "// Licensed under the Apache License, Version 2.0 (the \"License\");\n"
                        "// you may not use this file except in compliance with the License.\n"
                        "// You may obtain a copy of the License at\n"
                        "//\n"
                        "// http://www.apache.org/licenses/LICENSE-2.0\n"
                        "//\n"
                        "// Unless required by applicable law or agreed to in writing, software\n"
                        "// distributed under the License is distributed on an \"AS IS\" BASIS,\n"
                        "// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.\n"
                        "// See the License for the specific language governing permissions and\n"
                        "// limitations under the License.\n"
                        "//\n")
        self.file.write("#ifndef " + node.inst_name.upper() + "_HEADER\n")
        self.file.write("#define " + node.inst_name.upper() + "_HEADER\n\n\n")
    def enter_Reg(self, node):
        register_name = node.get_path("_",'_{index:d}')
        address = hex(node.absolute_address)
        self.file.write(("#define " + register_name.upper() + "\t(" + address + ")\n").expandtabs(80))
    def enter_Field(self, node):
        field_name = node.get_path("_",'_{index:d}')
        if node.width == 1:
            field_mask = hex(1 << node.low)
            self.file.write(("#define " + field_name.upper() + "_LOW" + "\t(" + str(node.low) + ")\n").expandtabs(80))
            self.file.write(("#define " + field_name.upper() + "_MASK" + "\t(" + field_mask + ")\n").expandtabs(80))
        elif node.low != 0 or node.high != 31:
            field_mask = hex(((2 << node.high) - 1) & ~((1 << node.low) -1))
            self.file.write(("#define " + field_name.upper() + "_LOW" + "\t(" + str(node.low) + ")\n").expandtabs(80))
            self.file.write(("#define " + field_name.upper() + "_MASK" + "\t(" + field_mask + ")\n").expandtabs(80))

    def exit_Addrmap(self, node):
        self.file.write("\n\n#endif")
        self.file.close()

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

    # checking if the out directory exists or not.
    if not os.path.exists(output_dir):

        # if the out directory is not present then create it.
        os.makedirs(output_dir)

    # Export a SystemVerilog implementation
    exporter = RegblockExporter()
    exporter.export(
        root, sys.argv[2],
        cpuif_cls=PassthroughCpuif,
        retime_read_response=False
    )

    # Export a UVM register model
    exporter = UVMExporter()
    exporter.export(root, os.path.join(output_dir, os.path.splitext(os.path.basename(sys.argv[1]))[0]) + "_uvm.sv")

    # Traverse the register model!
    walker = RDLWalker(unroll=True)
    listener = CHeaderPrintingListener(output_dir)
    pkglistener = SVPkgAppendingListener(output_dir)
    walker.walk(root, listener, pkglistener)

except RDLCompileError:
    # A compilation error occurred. Exit with error code
    sys.exit(1)
