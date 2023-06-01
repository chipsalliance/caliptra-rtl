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

`ifndef PV_REG_SAMPLE
    `define PV_REG_SAMPLE
    
    /*----------------------- PV_REG__PVCTRL SAMPLE FUNCTIONS -----------------------*/
    function void pv_reg__pvCtrl::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lock_bit_cg[bt]) this.lock_bit_cg[bt].sample(data[0 + bt]);
            foreach(clear_bit_cg[bt]) this.clear_bit_cg[bt].sample(data[1 + bt]);
            foreach(rsvd0_bit_cg[bt]) this.rsvd0_bit_cg[bt].sample(data[2 + bt]);
            foreach(rsvd1_bit_cg[bt]) this.rsvd1_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*lock*/  ,  data[1:1]/*clear*/  ,  data[2:2]/*rsvd0*/  ,  data[7:3]/*rsvd1*/   );
        end
    endfunction

    function void pv_reg__pvCtrl::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lock_bit_cg[bt]) this.lock_bit_cg[bt].sample(lock.get_mirrored_value() >> bt);
            foreach(clear_bit_cg[bt]) this.clear_bit_cg[bt].sample(clear.get_mirrored_value() >> bt);
            foreach(rsvd0_bit_cg[bt]) this.rsvd0_bit_cg[bt].sample(rsvd0.get_mirrored_value() >> bt);
            foreach(rsvd1_bit_cg[bt]) this.rsvd1_bit_cg[bt].sample(rsvd1.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( lock.get_mirrored_value()  ,  clear.get_mirrored_value()  ,  rsvd0.get_mirrored_value()  ,  rsvd1.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- PV_REG__PCRREG SAMPLE FUNCTIONS -----------------------*/
    function void pv_reg__pcrReg::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(data_bit_cg[bt]) this.data_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*data*/   );
        end
    endfunction

    function void pv_reg__pcrReg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(data_bit_cg[bt]) this.data_bit_cg[bt].sample(data.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data.get_mirrored_value()   );
        end
    endfunction

`endif