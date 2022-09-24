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
from peakrdl_regblock.cpuif.passthrough import PassthroughCpuif
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
        self.file.write("#ifndef " + node.inst_name.upper() + "_HEADER\n")
        self.file.write("#define " + node.inst_name.upper() + "_HEADER\n\n\n")
    def enter_Reg(self, node):
        register_name = node.get_path("_",'_{index:d}')
        address = hex(node.absolute_address)
        self.file.write(("#define " + register_name.upper() + "\t(" + address + ")\n").expandtabs(60))

    def exit_Addrmap(self, node):
        self.file.write("\n\n#endif")
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

    # Traverse the register model!
    walker = RDLWalker(unroll=True)
    listener = CHeaderPrintingListener(output_dir)
    walker.walk(root, listener) 
except RDLCompileError:
    # A compilation error occurred. Exit with error code
    sys.exit(1)
