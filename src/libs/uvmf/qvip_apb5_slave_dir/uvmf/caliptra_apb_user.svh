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
// CLASS: caliptra_apb_user
//
// This defines user sideband signals used for APB transactions
// in Caliptra soc_ifc environment.
// This is used to furnish PAUSER value to reg2apb adapter when invoking
// reg write/read calls.
// This class is derived from uvm_object, and used to populate the
// uvm_reg_item.extension member
//
//---------------------------------------------------------------
class caliptra_apb_user extends uvm_object;

  rand bit unsigned [apb5_master_0_params::PAUSER_WIDTH-1:0] addr_user = '1;

  function void set_addr_user(bit unsigned [apb5_master_0_params::PAUSER_WIDTH-1:0] value);
    this.addr_user = value;
  endfunction

  function bit unsigned [apb5_master_0_params::PAUSER_WIDTH-1:0] get_addr_user();
    return this.addr_user;
  endfunction

endclass
