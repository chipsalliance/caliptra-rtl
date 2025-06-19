// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// This file defines macros for generating module names in the caliptra_prim package.

`ifndef caliptra_prim_module_name_macros_SVH
`define caliptra_prim_module_name_macros_SVH

// Defines the default prefix for caliptra_prim generic modules.
// This can be overridden by defining CALIPTRA_PRIM_MODULE_PREFIX
// before including this file. If not defined, it defaults to
// 'caliptra_prim_generic'. The prim generic implementations can be found under
// ${CALIPTRA_ROOT}/src/caliptra_prim_generic/rtl
//
// For production use it is recommended to implement the technology-specific
// modules replacing the generic ones. Use the ${CALIPTRA_PRIM_ROOT} envar
// to point to the technology-specific implementation root directory.
`ifndef CALIPTRA_PRIM_MODULE_PREFIX
`define CALIPTRA_PRIM_MODULE_PREFIX caliptra_prim_generic
`endif // CALIPTRA_PRIM_MODULE_PREFIX

// Macro to generate the full module name for caliptra_prim modules.
// Usage: `CALIPTRA_PRIM_MODULE_NAME(module_name)
// This will result in caliptra_prim_generic_module_name
// if CALIPTRA_PRIM_MODULE_PREFIX is not defined.
`define CALIPTRA_PRIM_MODULE_NAME_EXPAND(prefix, name) prefix``_``name

`define CALIPTRA_PRIM_MODULE_NAME(__name) \
    `CALIPTRA_PRIM_MODULE_NAME_EXPAND(`CALIPTRA_PRIM_MODULE_PREFIX, __name)
 
`endif // caliptra_prim_module_name_macros_SVH
