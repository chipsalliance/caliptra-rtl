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

`ifndef caliptra_aaxi_ports_svh
`define caliptra_aaxi_ports_svh

class caliptra_aaxi_ports extends uvm_object;
    `uvm_object_utils(caliptra_aaxi_ports)

    virtual aaxi_intf m_ports_arr[AAXI_INTC_MASTER_CNT-1:0];
    virtual aaxi_intf s_ports_arr[AAXI_INTC_SLAVE_CNT -1:0];

    //==========================================
    // Function:    new
    // Description: Constructor
    //==========================================
    function new(
        string name       = "caliptra_aaxi_ports",
        int    num_master = AAXI_INTC_MASTER_CNT,
        int    num_slave  = AAXI_INTC_SLAVE_CNT
        );
        super.new(name);
    endfunction
endclass

`endif
