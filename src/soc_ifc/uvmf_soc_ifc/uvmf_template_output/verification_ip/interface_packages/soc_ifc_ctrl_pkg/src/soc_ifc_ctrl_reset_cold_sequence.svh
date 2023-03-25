//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION:
// This sequences randomizes the soc_ifc_ctrl transaction and sends it
// to the UVM driver.
//
// This sequence constructs and randomizes a soc_ifc_ctrl_transaction.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_ctrl_reset_cold_sequence
  extends soc_ifc_ctrl_reset_sequence_base ;

  `uvm_object_utils( soc_ifc_ctrl_reset_cold_sequence )

  //*****************************************************************
  function new(string name = "");
    super.new(name);
    warm_reset_only = 1'b0;
  endfunction: new

endclass: soc_ifc_ctrl_reset_cold_sequence
