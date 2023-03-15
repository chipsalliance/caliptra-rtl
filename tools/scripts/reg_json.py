#!/usr/bin/env python3
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

# This module imports a json register definition from OpenTitan and creates SystemRDL
# model.
# Note that OpenTitan uses a more "human readable" extension to json called hjson.
# To convert hjson -> json, run the following command:
#  hjson -j src.hjson > src.json

import json
import re

from systemrdl import RDLListener
from systemrdl import component as comp
from systemrdl.importer import RDLImporter
from systemrdl.node import FieldNode
from systemrdl.rdltypes import AccessType
from systemrdl.rdltypes import OnReadType
from systemrdl.rdltypes import OnWriteType


class JsonImporter(RDLImporter):

  def import_file(self, path: str) -> None:
    super().import_file(path)

    # Load the JSON from a file and convert it to primitive Python objects
    with open(path, 'r', encoding='utf-8') as f:
      json_obj = json.load(f)

    # Decode the JSON object
    # Set is_top=True so that decode returns a definition rather than an instance
    top_addrmap_def = self.decode_addrmap(json_obj, is_top=True)

    # Register the top definition in the root namespace
    self.register_root_component(top_addrmap_def)

  def parse_digits(self, digits):
    # return lsb, msb for a given string input
    # Have: 4:3
    # Want: msb = 4, lsb = 3
    # Have: 4
    # Want: msb = 4, lsb = 3

    msb = digits
    lsb = digits
    if ':' in digits:
      pattern = re.compile(r'(\d+):(\d+)')
      match = pattern.match(digits)
      if match:
        msb = match.group(1)
        lsb = match.group(2)
      else:
        self.msg.fatal(
            "invalid bits found in '%s'" % bits, self.default_src_ref
        )

    return msb, lsb

  def decode_field(self, reg_obj, field_obj: dict) -> comp.Field:
    # Apply parent name if it is not set
    name = reg_obj['name']
    if 'name' in field_obj:
      name = field_obj['name']

    # validate that this json object contains all the required fields
    if 'bits' not in field_obj:
      self.msg.fatal(
          "'%s' object is missing 'bits'" % name, self.default_src_ref
      )
    if 'desc' not in field_obj:
      field_obj['desc'] = reg_obj['desc']

    # Create an RDL field definition
    comp_def = self.create_field_definition()

    msb, lsb = self.parse_digits(field_obj['bits'])

    # Apply reset property if it was set
    if 'resval' in field_obj:
      resval = str(field_obj['resval'])
      if 'False' in resval:
        resval = 9
      elif 'True' in resval:
        resval = 6
      else:
        resval = int(resval, 16)
      self.assign_property(comp_def, 'reset', resval)

    self.assign_property(comp_def, 'desc', field_obj['desc'])

    # decode and apply the sw access property.
    # All fields in a register have the same access type
    access_type = reg_obj['swaccess']
    if access_type == 'rw0c':
      self.assign_property(comp_def, 'sw', AccessType['rw'])
      self.assign_property(comp_def, 'onwrite', OnWriteType['wzc'])
    if access_type == 'rw0c':
      self.assign_property(comp_def, 'sw', AccessType['rw'])
      self.assign_property(comp_def, 'onwrite', OnWriteType['woclr'])
    elif access_type == 'rw':
      self.assign_property(comp_def, 'sw', AccessType['rw'])
    elif access_type == 'ro':
      self.assign_property(comp_def, 'sw', AccessType['r'])
    elif access_type == 'wo':
      self.assign_property(comp_def, 'sw', AccessType['w'])
    else:
      self.msg.fatal(
          'Undefined access_type: %s' % access_type, self.default_src_ref
      )

    # Instantiate the component definition
    inst = self.instantiate_field(
        comp_def, name, int(lsb), int(msb) - int(lsb) + 1
    )
    return inst

  def decode_reg(self, reg_obj: dict, addr: int) -> comp.Reg:
    # validate that this json object contains all the required fields
    if 'name' not in reg_obj:
      self.msg.fatal("JSON object is missing 'name'", self.default_src_ref)
    if 'desc' not in reg_obj:
      self.msg.fatal(
          "'%s' is missing 'desc'", reg_obj['name'], self.default_src_ref
      )
    if 'swaccess' not in reg_obj:
      self.msg.fatal(
          "'%s' is missing 'swaccess'", reg_obj['name'], self.default_src_ref
      )
    if 'hwaccess' not in reg_obj:
      self.msg.fatal(
          "'%s' is missing 'hwaccess'", reg_obj['name'], self.default_src_ref
      )
    if 'fields' not in reg_obj:
      self.msg.fatal(
          "'%s' is missing 'fields'", reg_obj['name'], self.default_src_ref
      )

    comp_def = self.create_reg_definition()

    # Collect children
    for field in reg_obj['fields']:
      # Convert each child component and add it to our reg definition
      child_inst = self.decode_field(reg_obj, field)
      self.add_child(comp_def, child_inst)

    # Convert the definition into an instance
    inst = self.instantiate_reg(comp_def, reg_obj['name'], addr)
    return inst

  def decode_addrmap(
      self, json_obj: dict, is_top: bool = False
  ) -> comp.Addrmap:
    # validate that this json object contains all the required fields
    if 'name' not in json_obj:
      self.msg.fatal("JSON object is missing 'name'", self.default_src_ref)
    if 'registers' not in json_obj:
      self.msg.fatal(
          "'%s' is missing 'registers'" % json_obj['name'], self.default_src_ref
      )

    if is_top:
      # if this is the top node, then instantiation is skipped, and the
      # definition inherits the inst name as its type name

      # For everything else, convert the definition into an instance
      comp_def = self.create_addrmap_definition(json_obj['name'])
    else:
      # otherwise, create an anonymous definition
      comp_def = self.create_addrmap_definition()

    addr = 0
    for index in range(4):
      child_inst = self.add_common_reg(json_obj, index * 4)
      self.add_child(comp_def, child_inst)
      addr += 4

    # Collect child registers
    for register in json_obj['registers']:
      child_inst = self.decode_reg(register, addr)
      addr += 4

      # Add the child component to this
      self.add_child(comp_def, child_inst)

    if is_top:
      # keep top-level addrmap as a definition. Skip instantiation
      return comp_def

    inst = self.instantiate_addrmap(
        comp_def, addrmap_name, json_obj['addr_offset']
    )
    return inst

  def add_common_reg(self, reg_obj: dict, addr: int) -> comp.Reg:
    # OpenTitan defines interrupts and alerts in the 'interrupt_list'
    # and 'alert_list'properties in the json.
    # register definitions.
    # 0x0 - Interrupt State Register
    # 0x4 - Interrupt Enable Register
    # 0x8 - Interrupt Test Register
    # 0xC - Alert Test Register

    # validate that this json object contains all the required fields
    if 'interrupt_list' not in reg_obj:
      self.msg.fatal(
          "JSON object is missing 'interrupt_list'", self.default_src_ref
      )
    if 'alert_list' not in reg_obj:
      self.msg.fatal(
          "JSON object is missing 'alert_list'", self.default_src_ref
      )

    comp_def = self.create_reg_definition()

    if addr == 0x0:
      reg_name = 'interrupt_state'
    elif addr == 0x4:
      reg_name = 'interrupt_enable'
    elif addr == 0x8:
      reg_name = 'interrupt_test'
    elif addr == 0xC:
      reg_name = 'alert_test'
    else:
      self.msg.fatal(
          'addr: %d is not supported in add_common_reg ' % addr,
          self.default_src_ref,
      )
    # Collect children
    fields = reg_obj['interrupt_list']
    if addr == 0xC:
      fields = reg_obj['alert_list']

    for index, field in enumerate(fields):
      if 'name' not in field:
        self.msg.fatal("field object is missing 'name'", self.default_src_ref)
      if 'desc' not in field:
        self.msg.fatal(
            "'%s' object is missing 'desc'" % name, self.default_src_ref
        )

      field_def = self.create_field_definition()

      field_name = field['name']
      field_desc = field['desc']

      if addr == 0x0:
        self.assign_property(field_def, 'sw', AccessType['rw'])
        self.assign_property(field_def, 'onwrite', OnWriteType['woclr'])
      elif addr == 0x4:
        field_desc = 'Enable interrupt when %s is set.' % field_name
        self.assign_property(field_def, 'sw', AccessType['rw'])
        self.assign_property(field_def, 'onwrite', OnWriteType['woclr'])
      elif addr == 0x8:
        field_desc = 'Write 1 to force %s to 1.' % field_name
        self.assign_property(field_def, 'sw', AccessType['w'])
      elif addr == 0xC:
        field_desc = 'Write 1 to trigger one alert event of this kind.'
        self.assign_property(field_def, 'sw', AccessType['w'])

      self.assign_property(field_def, 'desc', field_desc)

      # Instantiate the component definition
      bit_offset = index
      bit_width = 1
      field_inst = self.instantiate_field(
          field_def, field_name.upper(), bit_offset, bit_width
      )

      # Convert each child component and add it to our reg definition
      self.add_child(comp_def, field_inst)

    # Convert the definition into an instance
    inst = self.instantiate_reg(comp_def, reg_name.upper(), addr)

    return inst


# -------------------------------------------------------------------------------


# Define a listener that will print out the register model hierarchy
class MyModelPrintingListener(RDLListener):

  def __init__(self):
    self.indent = 0

  def enter_Component(self, node):
    if not isinstance(node, FieldNode):
      print('\t' * self.indent, node.get_path_segment())
      self.indent += 1

  def enter_Field(self, node):
    # Print some stuff about the field
    bit_range_str = '[%d:%d]' % (node.high, node.low)
    sw_access_str = 'sw=%s' % node.get_property('sw').name
    print(
        '\t' * self.indent,
        bit_range_str,
        node.get_path_segment(),
        sw_access_str,
    )

  def exit_Component(self, node):
    if not isinstance(node, FieldNode):
      self.indent -= 1


# -------------------------------------------------------------------------------

if __name__ == '__main__':
  import sys
  import os

  from systemrdl import RDLCompiler, RDLCompileError, RDLWalker
  from systemrdl.messages import FileSourceRef
  from peakrdl_systemrdl import SystemRDLExporter

  # Create a compiler session, and an importer attached to it
  rdlc = RDLCompiler()
  json_importer = JsonImporter(rdlc)

  # import each JSON file provided from the command line
  input_files = sys.argv[1:]
  try:
    for input_file in input_files:
      # compile or import based on the file extension
      ext = os.path.splitext(input_file)[1]
      if ext == '.rdl':
        rdlc.compile_file(input_file)
      elif ext == '.json':
        json_importer.import_file(input_file)
      else:
        rdlc.msg.fatal(
            'Unknown file extension: %s' % ext, FileSourceRef(input_file)
        )
    # Elaborate when done
    root = rdlc.elaborate()
  except RDLCompileError:
    sys.exit(1)

  # Export SystemRDL
  rdl_output_dir = os.path.abspath(os.path.dirname(sys.argv[1]))
  rdl_output_file = os.path.splitext(os.path.basename(sys.argv[1]))[0] + '.rdl'
  exporter = SystemRDLExporter()
  exporter.export(root, os.path.join(rdl_output_dir, rdl_output_file))

  # Display the imported model
  walker = RDLWalker()
  listener = MyModelPrintingListener()
  walker.walk(root, listener)
