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

//---------------------------------------------------------------
// CLASS: caliptra_axi_user
//
// This defines user sideband signals used for AXI transactions
// in Caliptra soc_ifc environment.
// This is used to furnish AxUSER value to reg2axi adapter when invoking
// reg write/read calls.
// This class is derived from uvm_object, and used to populate the
// uvm_reg_item.extension member
//
//---------------------------------------------------------------
class caliptra_axi_user extends uvm_object;

  rand bit unsigned [aaxi_pkg::AAXI_AWUSER_WIDTH-1:0] addr_user = '1;
  bit unsigned [15:0] ar_valid_delay = 1;
  bit unsigned [15:0] resp_valid_ready_delay = 1;
  bit unsigned [15:0] aw_valid_delay = 1;
  bit unsigned [15:0] b_valid_ready_delay = 1;
  bit unsigned [7:0] len = 0;
  bit unsigned [1:0] burst = 0;
  bit unsigned [3:0] wstrb [255:0];

  function new (string name="");
      super.new(name);
      if (aaxi_pkg::AAXI_AWUSER_WIDTH != aaxi_pkg::AAXI_ARUSER_WIDTH)
          `uvm_fatal("CALIPTRA_AXI_USER", $sformatf("AWUSER WIDTH [%0d] does not match ARUSER WIDTH [%0d]!", aaxi_pkg::AAXI_AWUSER_WIDTH, aaxi_pkg::AAXI_ARUSER_WIDTH))
      if (aaxi_pkg::AAXI_AWUSER_WIDTH != 32)
          `uvm_fatal("CALIPTRA_AXI_USER", $sformatf("AxUSER WIDTH [%0d] is invalid - expected [%0d]!", aaxi_pkg::AAXI_AWUSER_WIDTH, 32))
      // `uvm_info("KNU_USER_OBJ", "Setting default wstrb values to 'hf", UVM_MEDIUM)
      for (int i = 0; i < 256; i++)
        this.wstrb[i] = 'hf;
  endfunction

  function void set_addr_user(bit unsigned [aaxi_pkg::AAXI_AWUSER_WIDTH-1:0] value);
    this.addr_user = value;
  endfunction

  function bit unsigned [aaxi_pkg::AAXI_AWUSER_WIDTH-1:0] get_addr_user();
    return this.addr_user;
  endfunction

  function void set_ar_valid_delay(bit unsigned [15:0] value);
    `uvm_info("KNU_USER_OBJ", $sformatf("setting arvalid delay = %d", value), UVM_MEDIUM)
    this.ar_valid_delay = value;
endfunction

function bit unsigned [15:0] get_ar_valid_delay();
    return this.ar_valid_delay;
endfunction

function void set_resp_valid_ready_delay(bit unsigned [15:0] value);
    this.resp_valid_ready_delay = value;
endfunction

function bit unsigned [15:0] get_resp_valid_ready_delay();
  return this.resp_valid_ready_delay;
endfunction

function void set_aw_valid_delay(bit unsigned [15:0] value);
    this.aw_valid_delay = value;
endfunction

function bit unsigned [15:0] get_aw_valid_delay();
  return this.aw_valid_delay;
endfunction

function void set_b_valid_ready_delay(bit unsigned [15:0] value);
    this.b_valid_ready_delay = value;
endfunction

function bit unsigned [15:0] get_b_valid_ready_delay();
  return this.b_valid_ready_delay;
endfunction

function void set_len(bit unsigned [7:0] value);
  this.len = value;
endfunction

function bit unsigned [7:0] get_len();
  return this.len;
endfunction

function void set_burst(bit unsigned [1:0] value);
  this.burst = value;
endfunction

function bit unsigned [1:0] get_burst();
  return this.burst;
endfunction


endclass
