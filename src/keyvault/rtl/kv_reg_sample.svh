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

`ifndef KV_REG_SAMPLE
    `define KV_REG_SAMPLE
    
    /*----------------------- KV_REG__KVCTRL SAMPLE FUNCTIONS -----------------------*/
    function void kv_reg__kvCtrl::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lock_wr_bit_cg[bt]) this.lock_wr_bit_cg[bt].sample(data[0 + bt]);
            foreach(lock_use_bit_cg[bt]) this.lock_use_bit_cg[bt].sample(data[1 + bt]);
            foreach(clear_bit_cg[bt]) this.clear_bit_cg[bt].sample(data[2 + bt]);
            foreach(rsvd0_bit_cg[bt]) this.rsvd0_bit_cg[bt].sample(data[3 + bt]);
            foreach(rsvd1_bit_cg[bt]) this.rsvd1_bit_cg[bt].sample(data[4 + bt]);
            foreach(dest_valid_bit_cg[bt]) this.dest_valid_bit_cg[bt].sample(data[9 + bt]);
            foreach(last_dword_bit_cg[bt]) this.last_dword_bit_cg[bt].sample(data[17 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*lock_wr*/  ,  data[1:1]/*lock_use*/  ,  data[2:2]/*clear*/  ,  data[3:3]/*rsvd0*/  ,  data[8:4]/*rsvd1*/  ,  data[16:9]/*dest_valid*/  ,  data[20:17]/*last_dword*/   );
        end
    endfunction

    function void kv_reg__kvCtrl::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lock_wr_bit_cg[bt]) this.lock_wr_bit_cg[bt].sample(lock_wr.get_mirrored_value() >> bt);
            foreach(lock_use_bit_cg[bt]) this.lock_use_bit_cg[bt].sample(lock_use.get_mirrored_value() >> bt);
            foreach(clear_bit_cg[bt]) this.clear_bit_cg[bt].sample(clear.get_mirrored_value() >> bt);
            foreach(rsvd0_bit_cg[bt]) this.rsvd0_bit_cg[bt].sample(rsvd0.get_mirrored_value() >> bt);
            foreach(rsvd1_bit_cg[bt]) this.rsvd1_bit_cg[bt].sample(rsvd1.get_mirrored_value() >> bt);
            foreach(dest_valid_bit_cg[bt]) this.dest_valid_bit_cg[bt].sample(dest_valid.get_mirrored_value() >> bt);
            foreach(last_dword_bit_cg[bt]) this.last_dword_bit_cg[bt].sample(last_dword.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( lock_wr.get_mirrored_value()  ,  lock_use.get_mirrored_value()  ,  clear.get_mirrored_value()  ,  rsvd0.get_mirrored_value()  ,  rsvd1.get_mirrored_value()  ,  dest_valid.get_mirrored_value()  ,  last_dword.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_REG__KEYREG SAMPLE FUNCTIONS -----------------------*/
    function void kv_reg__keyReg::sample(uvm_reg_data_t  data,
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

    function void kv_reg__keyReg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(data_bit_cg[bt]) this.data_bit_cg[bt].sample(data.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_REG__CLEAR_SECRETS SAMPLE FUNCTIONS -----------------------*/
    function void kv_reg__CLEAR_SECRETS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(wr_debug_values_bit_cg[bt]) this.wr_debug_values_bit_cg[bt].sample(data[0 + bt]);
            foreach(sel_debug_value_bit_cg[bt]) this.sel_debug_value_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*wr_debug_values*/  ,  data[1:1]/*sel_debug_value*/   );
        end
    endfunction

    function void kv_reg__CLEAR_SECRETS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(wr_debug_values_bit_cg[bt]) this.wr_debug_values_bit_cg[bt].sample(wr_debug_values.get_mirrored_value() >> bt);
            foreach(sel_debug_value_bit_cg[bt]) this.sel_debug_value_bit_cg[bt].sample(sel_debug_value.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( wr_debug_values.get_mirrored_value()  ,  sel_debug_value.get_mirrored_value()   );
        end
    endfunction

`endif