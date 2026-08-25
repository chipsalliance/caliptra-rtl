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

import json
import sys
import tempfile
import unittest
from pathlib import Path

from systemrdl import RDLCompiler, RDLListener, RDLWalker
from systemrdl.node import FieldNode

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from reg_json import JsonImporter  # noqa: E402


class FieldPropertyListener(RDLListener):

  def __init__(self):
    self.fields = {}

  def enter_Field(self, node: FieldNode) -> None:
    key = (node.parent.inst_name, node.inst_name)
    self.fields[key] = {
        'sw': self._property_name(node, 'sw'),
        'onwrite': self._property_name(node, 'onwrite'),
    }

  @staticmethod
  def _property_name(node: FieldNode, name: str):
    value = node.get_property(name)
    return None if value is None else value.name


class JsonImporterAccessTest(unittest.TestCase):

  def test_access_properties(self):
    register_description = {
        'name': 'access_probe',
        'interrupt_list': [{'name': 'irq', 'desc': 'Interrupt.'}],
        'alert_list': [{'name': 'alert', 'desc': 'Alert.'}],
        'registers': [
            {
                'name': 'ORDINARY_RW',
                'desc': 'Ordinary read/write.',
                'swaccess': 'rw',
                'hwaccess': 'hro',
                'fields': [{'name': 'VALUE', 'bits': '0', 'desc': 'Value.'}],
            },
            {
                'name': 'WRITE_ZERO_CLEAR',
                'desc': 'Write zero to clear.',
                'swaccess': 'rw0c',
                'hwaccess': 'hrw',
                'fields': [{'name': 'VALUE', 'bits': '0', 'desc': 'Value.'}],
            },
        ],
    }

    with tempfile.TemporaryDirectory() as directory:
      input_path = Path(directory) / 'access_probe.json'
      input_path.write_text(json.dumps(register_description), encoding='utf-8')

      compiler = RDLCompiler()
      JsonImporter(compiler).import_file(str(input_path))
      root = compiler.elaborate()

    listener = FieldPropertyListener()
    RDLWalker().walk(root, listener)

    self.assertEqual(
        listener.fields,
        {
            ('INTERRUPT_STATE', 'IRQ'): {'sw': 'rw', 'onwrite': 'woclr'},
            ('INTERRUPT_ENABLE', 'IRQ'): {'sw': 'rw', 'onwrite': None},
            ('INTERRUPT_TEST', 'IRQ'): {'sw': 'w', 'onwrite': None},
            ('ALERT_TEST', 'ALERT'): {'sw': 'w', 'onwrite': None},
            ('ORDINARY_RW', 'VALUE'): {'sw': 'rw', 'onwrite': None},
            ('WRITE_ZERO_CLEAR', 'VALUE'): {'sw': 'rw', 'onwrite': 'wzc'},
        },
    )


if __name__ == '__main__':
  unittest.main()
