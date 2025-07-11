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
import argparse

# Parse command line arguments
parser = argparse.ArgumentParser(description='Generate register documentation from RDL files')
parser.add_argument('files', nargs='+', help='RDL or JSON input files')
parser.add_argument('--param', '-p', action='append', default=[], 
                    help='Set RDL parameter (format: NAME=VALUE). Can be used multiple times.')
args = parser.parse_args()

# Process input files from parsed args
input_files = args.files

#output directory for dumping files
filename = os.path.splitext(os.path.basename(input_files[0]))[0]
rtl_output_dir = os.path.abspath(os.path.dirname(input_files[0]))
html_output_dir = os.path.join(rtl_output_dir, '..', 'docs', filename + "_html")
doc_output_dir = os.path.join(rtl_output_dir, '..', 'docs')

# Listener block will print register name and address into C Header file
class HeaderPrintingListener(RDLListener):
    def __init__(self, file_path, filename, ext, tick, do_global=1, do_rel=1):
        self.regfile_offset = 0
        self.tick = tick
        self.do_global = do_global
        self.do_rel = do_rel
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
        if self.do_global == 1:
            self.file.write((self.tick + "define " + register_name.upper() + "_BASE_ADDR" + "\t(" + address + ")\n").expandtabs(100))
    def enter_Regfile(self, node):
        self.regfile_offset = node.address_offset
        register_name = node.get_path("_",'_{index:d}')
        address = hex(node.absolute_address)
        if self.tick == "`":
            address = address.replace("0x", "32'h", 1)
        if self.do_global == 1:
            self.file.write((self.tick + "define " + register_name.upper() + "_START" + "\t(" + address + ")\n").expandtabs(100))
    def exit_Regfile(self, node):
        self.regfile_offset = 0
    def enter_Reg(self, node):
        #getting and printing the absolute address and path for each register
        register_name = node.get_path("_",'_{index:d}')
        address = hex(node.absolute_address)
        if self.tick == "`":
            address = address.replace("0x", "32'h", 1)
        if self.do_global == 1:
            self.file.write((self.tick + "define " + register_name.upper() + "\t(" + address + ")\n").expandtabs(100))
        #getting and printing the relative address and path for each register (relative to the addr map it belongs to)
        register_name = node.get_rel_path(self.top_node.parent,"^","_",'_{index:d}')
        address = hex(node.address_offset + self.regfile_offset)
        if self.tick == "`":
            address = address.replace("0x", "32'h", 1)
        if self.do_rel == 1:
            self.file.write( self.tick + "ifndef " + register_name.upper() + "\n")
            self.file.write((self.tick + "define " + register_name.upper() + "\t(" + address + ")\n").expandtabs(100))
    def exit_Reg(self, node):
        if self.do_rel == 1:
            self.file.write( self.tick + "endif\n")
    def enter_Field(self, node):
        field_name = node.get_rel_path(self.top_node.parent,"^","_",'_{index:d}')
        if node.width == 1:
            field_mask = hex(1 << node.low)
            if self.tick == "`":
                field_mask = field_mask.replace("0x", "32'h", 1)
            if self.do_rel == 1:
                self.file.write((self.tick + "define " + field_name.upper() + "_LOW" + "\t(" + str(node.low) + ")\n").expandtabs(100))
                self.file.write((self.tick + "define " + field_name.upper() + "_MASK" + "\t(" + field_mask + ")\n").expandtabs(100))
        elif node.low != 0 or node.high != 31:
            field_mask = hex(((2 << node.high) - 1) & ~((1 << node.low) -1))
            if self.tick == "`":
                field_mask = field_mask.replace("0x", "32'h", 1)
            if self.do_rel == 1:
                self.file.write((self.tick + "define " + field_name.upper() + "_LOW" + "\t(" + str(node.low) + ")\n").expandtabs(100))
                self.file.write((self.tick + "define " + field_name.upper() + "_MASK" + "\t(" + field_mask + ")\n").expandtabs(100))
    def enter_Mem(self, node):
        #getting and printing the absolute address and path for each register
        mem_name = node.get_path("_",'_{index:d}')
        address = hex(node.absolute_address)
        if self.tick == "`":
            address = address.replace("0x", "32'h", 1)
        if self.do_global == 1:
            self.file.write((self.tick + "define " + mem_name.upper() + "_BASE_ADDR" + "\t(" + address + ")\n").expandtabs(100))
        #getting and printing the end address for the memory
        address = hex(node.absolute_address + node.size - 1)
        if self.tick == "`":
            address = address.replace("0x", "32'h", 1)
        if self.do_global == 1:
            self.file.write((self.tick + "define " + mem_name.upper() + "_END_ADDR" + "\t(" + address + ")\n").expandtabs(100))



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

    # Build parameters dictionary from command line arguments
    parameters = {}
    for param in args.param:
        if '=' not in param:
            print(f"Error: Invalid parameter format '{param}'. Use NAME=VALUE")
            sys.exit(1)
        name, value = param.split('=', 1)

        # Handle boolean values - only accept 'true' or 'false'
        if value.lower() in ['true', 'false']:
            parameters[name] = value.lower() == 'true'
        # Handle hex values
        elif value.startswith('0x'):
            try:
                parameters[name] = int(value, 16)
            except ValueError:
                print(f"Error: Invalid hex value '{value}'")
                sys.exit(1)
        # Handle integer values
        elif value.isdigit() or (value.startswith('-') and value[1:].isdigit()):
            parameters[name] = int(value)
        # Default to string
        else:
            parameters[name] = value


    # Elaborate the design
    root = rdlc.elaborate(parameters=parameters if parameters else None)

    # checking if the html out directory exists or not.
    if os.path.exists(html_output_dir):
        # delete the html directory, the file names aren't always the same
        shutil.rmtree(html_output_dir)
    # create it again
    os.makedirs(html_output_dir)

    # Export documentation in HTML
    exporter = HTMLExporter(extra_doc_properties=["resetsignal", "swwe"], show_signals=True)
    exporter.export(root, html_output_dir)

    # Traverse the register model
    walker = RDLWalker(unroll=True)
    listener = HeaderPrintingListener(rtl_output_dir, filename, ".h", "#")
    walker.walk(root, listener)
    listener.file.write("\n\n#endif")
    listener.file.close()
    listener = HeaderPrintingListener(rtl_output_dir, filename + "_defines", ".svh", "`", 1, 0)
    walker.walk(root, listener)
    listener.file.write("\n\n`endif")
    listener.file.close()
    listener = HeaderPrintingListener(rtl_output_dir, filename + "_field_defines", ".svh", "`", 0, 1)
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
