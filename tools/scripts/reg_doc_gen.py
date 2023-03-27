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
from reg_json import JsonImporter
from math import log, ceil
import sys
import os
import shutil

#output directory for dumping files
filename = os.path.splitext(os.path.basename(sys.argv[1]))[0]
rtl_output_dir = os.path.abspath(os.path.dirname(sys.argv[1]))
html_output_dir = os.path.join(rtl_output_dir, '..', 'docs', filename + "_html")
doc_output_dir = os.path.join(rtl_output_dir, '..', 'docs')

# Listener block will print register name and address into C Header file
class HeaderPrintingListener(RDLListener):
    def __init__(self, file_path, filename, ext, tick):
        self.regfile_offset = 0
        self.tick = tick
        self.file_path = file_path
        header_file_path = os.path.join(self.file_path, filename + ext)
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
        self.file.write(self.tick + "ifndef " + filename.upper() + "_HEADER\n")
        self.file.write(self.tick + "define " + filename.upper() + "_HEADER\n\n\n")
    def enter_Addrmap(self, node):
        #save reference to addrmap top for relative path
        self.top_node = node
        register_name = node.get_path("_",'_{index:d}')
        address = hex(node.absolute_address)
        if self.tick == "`":
            address = address.replace("0x", "32'h", 1)
        #print the base address of each address map
        self.file.write((self.tick + "define " + register_name.upper() + "_BASE_ADDR" + "\t(" + address + ")\n").expandtabs(100))
    def enter_Regfile(self, node):
        self.regfile_offset = node.address_offset
        register_name = node.get_path("_",'_{index:d}')
        address = hex(node.absolute_address)
        if self.tick == "`":
            address = address.replace("0x", "32'h", 1)
        self.file.write((self.tick + "define " + register_name.upper() + "_START" + "\t(" + address + ")\n").expandtabs(100))
    def exit_Regfile(self, node):
        self.regfile_offset = 0
    def enter_Reg(self, node):
        #getting and printing the absolute address and path for reach register
        register_name = node.get_path("_",'_{index:d}')
        address = hex(node.absolute_address)
        if self.tick == "`":
            address = address.replace("0x", "32'h", 1)
        self.file.write((self.tick + "define " + register_name.upper() + "\t(" + address + ")\n").expandtabs(100))
        #getting and printing the relative address and path for each register (relative to the addr map it belongs to)
        register_name = node.get_rel_path(self.top_node.parent,"^","_",'_{index:d}')
        address = hex(node.address_offset + self.regfile_offset)
        if self.tick == "`":
            address = address.replace("0x", "32'h", 1)
        self.file.write((self.tick + "define " + register_name.upper() + "\t(" + address + ")\n").expandtabs(100))
    def enter_Field(self, node):
        field_name = node.get_rel_path(self.top_node.parent,"^","_",'_{index:d}')
        if node.width == 1:
            field_mask = hex(1 << node.low)
            if self.tick == "`":
                field_mask = field_mask.replace("0x", "32'h", 1)
            self.file.write((self.tick + "define " + field_name.upper() + "_LOW" + "\t(" + str(node.low) + ")\n").expandtabs(100))
            self.file.write((self.tick + "define " + field_name.upper() + "_MASK" + "\t(" + field_mask + ")\n").expandtabs(100))
        elif node.low != 0 or node.high != 31:
            field_mask = hex(((2 << node.high) - 1) & ~((1 << node.low) -1))
            if self.tick == "`":
                field_mask = field_mask.replace("0x", "32'h", 1)
            self.file.write((self.tick + "define " + field_name.upper() + "_LOW" + "\t(" + str(node.low) + ")\n").expandtabs(100))
            self.file.write((self.tick + "define " + field_name.upper() + "_MASK" + "\t(" + field_mask + ")\n").expandtabs(100))


#list of address map files to compile
input_files = sys.argv[1:]

# Create an instance of the compiler
rdlc = RDLCompiler()
# Attach importer to rdlc instance
json_importer = JsonImporter(rdlc)

try:
    # Compile your RDL files, dependencies first
    for input_file in reversed(input_files):
      # compile or import based on the file extension
      ext = os.path.splitext(input_file)[1]
      if ext == ".json":
        json_importer.import_file(input_file)
      else:
        rdlc.compile_file(input_file)

    # Elaborate the design
    root = rdlc.elaborate()

    # checking if the html out directory exists or not.
    if os.path.exists(html_output_dir):
        # delete the html directory, the file names aren't always the same
        shutil.rmtree(html_output_dir)
    # create it again
    os.makedirs(html_output_dir)

    # Export documentation in HTML
    exporter = HTMLExporter(extra_doc_properties=["resetsignal"])
    exporter.export(root, html_output_dir)

    # Traverse the register model
    walker = RDLWalker(unroll=True)
    listener = HeaderPrintingListener(rtl_output_dir, filename, ".h", "#")
    walker.walk(root, listener)
    listener.file.write("\n\n#endif")
    listener.file.close()
    listener = HeaderPrintingListener(rtl_output_dir, filename + "_defines", ".svh", "`")
    walker.walk(root, listener)
    listener.file.write("\n\n`endif")
    listener.file.close()
    # This was going to print a svh file, but need to fix the address output so it looks like svh TODO
    #listener = HeaderPrintingListener(rtl_output_dir, filename, ".svh", "`")
    #walker.walk(root, listener)
    #listener.file.write("\n\n`endif")
    #listener.file.close()

except RDLCompileError:
    # A compilation error occurred. Exit with error code
    sys.exit(1)
