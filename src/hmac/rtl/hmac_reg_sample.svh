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

`ifndef HMAC_REG_SAMPLE
    `define HMAC_REG_SAMPLE
    
    /*----------------------- HMAC_REG__HMAC512_NAME SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__HMAC512_NAME::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(NAME_bit_cg[bt]) this.NAME_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*NAME*/   );
        end
    endfunction

    function void hmac_reg__HMAC512_NAME::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(NAME_bit_cg[bt]) this.NAME_bit_cg[bt].sample(NAME.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( NAME.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__HMAC512_VERSION SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__HMAC512_VERSION::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERSION_bit_cg[bt]) this.VERSION_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*VERSION*/   );
        end
    endfunction

    function void hmac_reg__HMAC512_VERSION::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERSION_bit_cg[bt]) this.VERSION_bit_cg[bt].sample(VERSION.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( VERSION.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__HMAC512_CTRL SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__HMAC512_CTRL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(INIT_bit_cg[bt]) this.INIT_bit_cg[bt].sample(data[0 + bt]);
            foreach(NEXT_bit_cg[bt]) this.NEXT_bit_cg[bt].sample(data[1 + bt]);
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(data[2 + bt]);
            foreach(MODE_bit_cg[bt]) this.MODE_bit_cg[bt].sample(data[3 + bt]);
            foreach(CSR_MODE_bit_cg[bt]) this.CSR_MODE_bit_cg[bt].sample(data[4 + bt]);
            foreach(LAST_bit_cg[bt]) this.LAST_bit_cg[bt].sample(data[5 + bt]);
            foreach(Reserved_bit_cg[bt]) this.Reserved_bit_cg[bt].sample(data[6 + bt]);
            foreach(RESTORE_bit_cg[bt]) this.RESTORE_bit_cg[bt].sample(data[7 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*INIT*/  ,  data[1:1]/*NEXT*/  ,  data[2:2]/*ZEROIZE*/  ,  data[3:3]/*MODE*/  ,  data[4:4]/*CSR_MODE*/  ,  data[5:5]/*LAST*/  ,  data[6:6]/*Reserved*/  ,  data[7:7]/*RESTORE*/   );
        end
    endfunction

    function void hmac_reg__HMAC512_CTRL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(INIT_bit_cg[bt]) this.INIT_bit_cg[bt].sample(INIT.get_mirrored_value() >> bt);
            foreach(NEXT_bit_cg[bt]) this.NEXT_bit_cg[bt].sample(NEXT.get_mirrored_value() >> bt);
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(ZEROIZE.get_mirrored_value() >> bt);
            foreach(MODE_bit_cg[bt]) this.MODE_bit_cg[bt].sample(MODE.get_mirrored_value() >> bt);
            foreach(CSR_MODE_bit_cg[bt]) this.CSR_MODE_bit_cg[bt].sample(CSR_MODE.get_mirrored_value() >> bt);
            foreach(LAST_bit_cg[bt]) this.LAST_bit_cg[bt].sample(LAST.get_mirrored_value() >> bt);
            foreach(Reserved_bit_cg[bt]) this.Reserved_bit_cg[bt].sample(Reserved.get_mirrored_value() >> bt);
            foreach(RESTORE_bit_cg[bt]) this.RESTORE_bit_cg[bt].sample(RESTORE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( INIT.get_mirrored_value()  ,  NEXT.get_mirrored_value()  ,  ZEROIZE.get_mirrored_value()  ,  MODE.get_mirrored_value()  ,  CSR_MODE.get_mirrored_value()  ,  LAST.get_mirrored_value()  ,  Reserved.get_mirrored_value()  ,  RESTORE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__HMAC512_STATUS SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__HMAC512_STATUS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(data[0 + bt]);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*READY*/  ,  data[1:1]/*VALID*/   );
        end
    endfunction

    function void hmac_reg__HMAC512_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(READY.get_mirrored_value() >> bt);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( READY.get_mirrored_value()  ,  VALID.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__HMAC512_KEY SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__HMAC512_KEY::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(KEY_bit_cg[bt]) this.KEY_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*KEY*/   );
        end
    endfunction

    function void hmac_reg__HMAC512_KEY::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(KEY_bit_cg[bt]) this.KEY_bit_cg[bt].sample(KEY.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( KEY.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__HMAC512_BLOCK SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__HMAC512_BLOCK::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(BLOCK_bit_cg[bt]) this.BLOCK_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*BLOCK*/   );
        end
    endfunction

    function void hmac_reg__HMAC512_BLOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(BLOCK_bit_cg[bt]) this.BLOCK_bit_cg[bt].sample(BLOCK.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( BLOCK.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__HMAC512_TAG SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__HMAC512_TAG::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(TAG_bit_cg[bt]) this.TAG_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*TAG*/   );
        end
    endfunction

    function void hmac_reg__HMAC512_TAG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(TAG_bit_cg[bt]) this.TAG_bit_cg[bt].sample(TAG.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( TAG.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__HMAC512_LFSR_SEED SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__HMAC512_LFSR_SEED::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LFSR_SEED_bit_cg[bt]) this.LFSR_SEED_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*LFSR_SEED*/   );
        end
    endfunction

    function void hmac_reg__HMAC512_LFSR_SEED::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LFSR_SEED_bit_cg[bt]) this.LFSR_SEED_bit_cg[bt].sample(LFSR_SEED.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LFSR_SEED.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_READ_CTRL_REG SAMPLE FUNCTIONS -----------------------*/
    function void kv_read_ctrl_reg::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(read_en_bit_cg[bt]) this.read_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(read_entry_bit_cg[bt]) this.read_entry_bit_cg[bt].sample(data[1 + bt]);
            foreach(pcr_hash_extend_bit_cg[bt]) this.pcr_hash_extend_bit_cg[bt].sample(data[6 + bt]);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(data[7 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*read_en*/  ,  data[5:1]/*read_entry*/  ,  data[6:6]/*pcr_hash_extend*/  ,  data[31:7]/*rsvd*/   );
        end
    endfunction

    function void kv_read_ctrl_reg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(read_en_bit_cg[bt]) this.read_en_bit_cg[bt].sample(read_en.get_mirrored_value() >> bt);
            foreach(read_entry_bit_cg[bt]) this.read_entry_bit_cg[bt].sample(read_entry.get_mirrored_value() >> bt);
            foreach(pcr_hash_extend_bit_cg[bt]) this.pcr_hash_extend_bit_cg[bt].sample(pcr_hash_extend.get_mirrored_value() >> bt);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(rsvd.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( read_en.get_mirrored_value()  ,  read_entry.get_mirrored_value()  ,  pcr_hash_extend.get_mirrored_value()  ,  rsvd.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_STATUS_REG SAMPLE FUNCTIONS -----------------------*/
    function void kv_status_reg::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(data[0 + bt]);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(data[1 + bt]);
            foreach(ERROR_bit_cg[bt]) this.ERROR_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*READY*/  ,  data[1:1]/*VALID*/  ,  data[9:2]/*ERROR*/   );
        end
    endfunction

    function void kv_status_reg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(READY.get_mirrored_value() >> bt);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
            foreach(ERROR_bit_cg[bt]) this.ERROR_bit_cg[bt].sample(ERROR.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( READY.get_mirrored_value()  ,  VALID.get_mirrored_value()  ,  ERROR.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_READ_CTRL_REG SAMPLE FUNCTIONS -----------------------*/
    function void kv_read_ctrl_reg::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(read_en_bit_cg[bt]) this.read_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(read_entry_bit_cg[bt]) this.read_entry_bit_cg[bt].sample(data[1 + bt]);
            foreach(pcr_hash_extend_bit_cg[bt]) this.pcr_hash_extend_bit_cg[bt].sample(data[6 + bt]);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(data[7 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*read_en*/  ,  data[5:1]/*read_entry*/  ,  data[6:6]/*pcr_hash_extend*/  ,  data[31:7]/*rsvd*/   );
        end
    endfunction

    function void kv_read_ctrl_reg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(read_en_bit_cg[bt]) this.read_en_bit_cg[bt].sample(read_en.get_mirrored_value() >> bt);
            foreach(read_entry_bit_cg[bt]) this.read_entry_bit_cg[bt].sample(read_entry.get_mirrored_value() >> bt);
            foreach(pcr_hash_extend_bit_cg[bt]) this.pcr_hash_extend_bit_cg[bt].sample(pcr_hash_extend.get_mirrored_value() >> bt);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(rsvd.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( read_en.get_mirrored_value()  ,  read_entry.get_mirrored_value()  ,  pcr_hash_extend.get_mirrored_value()  ,  rsvd.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_STATUS_REG SAMPLE FUNCTIONS -----------------------*/
    function void kv_status_reg::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(data[0 + bt]);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(data[1 + bt]);
            foreach(ERROR_bit_cg[bt]) this.ERROR_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*READY*/  ,  data[1:1]/*VALID*/  ,  data[9:2]/*ERROR*/   );
        end
    endfunction

    function void kv_status_reg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(READY.get_mirrored_value() >> bt);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
            foreach(ERROR_bit_cg[bt]) this.ERROR_bit_cg[bt].sample(ERROR.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( READY.get_mirrored_value()  ,  VALID.get_mirrored_value()  ,  ERROR.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_WRITE_CTRL_REG SAMPLE FUNCTIONS -----------------------*/
    function void kv_write_ctrl_reg::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(write_en_bit_cg[bt]) this.write_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(write_entry_bit_cg[bt]) this.write_entry_bit_cg[bt].sample(data[1 + bt]);
            foreach(hmac_key_dest_valid_bit_cg[bt]) this.hmac_key_dest_valid_bit_cg[bt].sample(data[6 + bt]);
            foreach(hmac_block_dest_valid_bit_cg[bt]) this.hmac_block_dest_valid_bit_cg[bt].sample(data[7 + bt]);
            foreach(mldsa_seed_dest_valid_bit_cg[bt]) this.mldsa_seed_dest_valid_bit_cg[bt].sample(data[8 + bt]);
            foreach(ecc_pkey_dest_valid_bit_cg[bt]) this.ecc_pkey_dest_valid_bit_cg[bt].sample(data[9 + bt]);
            foreach(ecc_seed_dest_valid_bit_cg[bt]) this.ecc_seed_dest_valid_bit_cg[bt].sample(data[10 + bt]);
            foreach(aes_key_dest_valid_bit_cg[bt]) this.aes_key_dest_valid_bit_cg[bt].sample(data[11 + bt]);
            foreach(mlkem_seed_dest_valid_bit_cg[bt]) this.mlkem_seed_dest_valid_bit_cg[bt].sample(data[12 + bt]);
            foreach(mlkem_msg_dest_valid_bit_cg[bt]) this.mlkem_msg_dest_valid_bit_cg[bt].sample(data[13 + bt]);
            foreach(dma_data_dest_valid_bit_cg[bt]) this.dma_data_dest_valid_bit_cg[bt].sample(data[14 + bt]);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(data[15 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*write_en*/  ,  data[5:1]/*write_entry*/  ,  data[6:6]/*hmac_key_dest_valid*/  ,  data[7:7]/*hmac_block_dest_valid*/  ,  data[8:8]/*mldsa_seed_dest_valid*/  ,  data[9:9]/*ecc_pkey_dest_valid*/  ,  data[10:10]/*ecc_seed_dest_valid*/  ,  data[11:11]/*aes_key_dest_valid*/  ,  data[12:12]/*mlkem_seed_dest_valid*/  ,  data[13:13]/*mlkem_msg_dest_valid*/  ,  data[14:14]/*dma_data_dest_valid*/  ,  data[31:15]/*rsvd*/   );
        end
    endfunction

    function void kv_write_ctrl_reg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(write_en_bit_cg[bt]) this.write_en_bit_cg[bt].sample(write_en.get_mirrored_value() >> bt);
            foreach(write_entry_bit_cg[bt]) this.write_entry_bit_cg[bt].sample(write_entry.get_mirrored_value() >> bt);
            foreach(hmac_key_dest_valid_bit_cg[bt]) this.hmac_key_dest_valid_bit_cg[bt].sample(hmac_key_dest_valid.get_mirrored_value() >> bt);
            foreach(hmac_block_dest_valid_bit_cg[bt]) this.hmac_block_dest_valid_bit_cg[bt].sample(hmac_block_dest_valid.get_mirrored_value() >> bt);
            foreach(mldsa_seed_dest_valid_bit_cg[bt]) this.mldsa_seed_dest_valid_bit_cg[bt].sample(mldsa_seed_dest_valid.get_mirrored_value() >> bt);
            foreach(ecc_pkey_dest_valid_bit_cg[bt]) this.ecc_pkey_dest_valid_bit_cg[bt].sample(ecc_pkey_dest_valid.get_mirrored_value() >> bt);
            foreach(ecc_seed_dest_valid_bit_cg[bt]) this.ecc_seed_dest_valid_bit_cg[bt].sample(ecc_seed_dest_valid.get_mirrored_value() >> bt);
            foreach(aes_key_dest_valid_bit_cg[bt]) this.aes_key_dest_valid_bit_cg[bt].sample(aes_key_dest_valid.get_mirrored_value() >> bt);
            foreach(mlkem_seed_dest_valid_bit_cg[bt]) this.mlkem_seed_dest_valid_bit_cg[bt].sample(mlkem_seed_dest_valid.get_mirrored_value() >> bt);
            foreach(mlkem_msg_dest_valid_bit_cg[bt]) this.mlkem_msg_dest_valid_bit_cg[bt].sample(mlkem_msg_dest_valid.get_mirrored_value() >> bt);
            foreach(dma_data_dest_valid_bit_cg[bt]) this.dma_data_dest_valid_bit_cg[bt].sample(dma_data_dest_valid.get_mirrored_value() >> bt);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(rsvd.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( write_en.get_mirrored_value()  ,  write_entry.get_mirrored_value()  ,  hmac_key_dest_valid.get_mirrored_value()  ,  hmac_block_dest_valid.get_mirrored_value()  ,  mldsa_seed_dest_valid.get_mirrored_value()  ,  ecc_pkey_dest_valid.get_mirrored_value()  ,  ecc_seed_dest_valid.get_mirrored_value()  ,  aes_key_dest_valid.get_mirrored_value()  ,  mlkem_seed_dest_valid.get_mirrored_value()  ,  mlkem_msg_dest_valid.get_mirrored_value()  ,  dma_data_dest_valid.get_mirrored_value()  ,  rsvd.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_STATUS_REG SAMPLE FUNCTIONS -----------------------*/
    function void kv_status_reg::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(data[0 + bt]);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(data[1 + bt]);
            foreach(ERROR_bit_cg[bt]) this.ERROR_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*READY*/  ,  data[1:1]/*VALID*/  ,  data[9:2]/*ERROR*/   );
        end
    endfunction

    function void kv_status_reg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(READY.get_mirrored_value() >> bt);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
            foreach(ERROR_bit_cg[bt]) this.ERROR_bit_cg[bt].sample(ERROR.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( READY.get_mirrored_value()  ,  VALID.get_mirrored_value()  ,  ERROR.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__GLOBAL_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__global_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_en*/  ,  data[1:1]/*notif_en*/   );
        end
    endfunction

    function void hmac_reg__global_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(error_en.get_mirrored_value() >> bt);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(notif_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_en.get_mirrored_value()  ,  notif_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__ERROR_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__error_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_mode_error_en_bit_cg[bt]) this.key_mode_error_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(key_zero_error_en_bit_cg[bt]) this.key_zero_error_en_bit_cg[bt].sample(data[1 + bt]);
            foreach(error2_en_bit_cg[bt]) this.error2_en_bit_cg[bt].sample(data[2 + bt]);
            foreach(error3_en_bit_cg[bt]) this.error3_en_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*key_mode_error_en*/  ,  data[1:1]/*key_zero_error_en*/  ,  data[2:2]/*error2_en*/  ,  data[3:3]/*error3_en*/   );
        end
    endfunction

    function void hmac_reg__error_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_mode_error_en_bit_cg[bt]) this.key_mode_error_en_bit_cg[bt].sample(key_mode_error_en.get_mirrored_value() >> bt);
            foreach(key_zero_error_en_bit_cg[bt]) this.key_zero_error_en_bit_cg[bt].sample(key_zero_error_en.get_mirrored_value() >> bt);
            foreach(error2_en_bit_cg[bt]) this.error2_en_bit_cg[bt].sample(error2_en.get_mirrored_value() >> bt);
            foreach(error3_en_bit_cg[bt]) this.error3_en_bit_cg[bt].sample(error3_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( key_mode_error_en.get_mirrored_value()  ,  key_zero_error_en.get_mirrored_value()  ,  error2_en.get_mirrored_value()  ,  error3_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__NOTIF_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__notif_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_en_bit_cg[bt]) this.notif_cmd_done_en_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_done_en*/   );
        end
    endfunction

    function void hmac_reg__notif_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_en_bit_cg[bt]) this.notif_cmd_done_en_bit_cg[bt].sample(notif_cmd_done_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__GLOBAL_INTR_T_AGG_STS_DD3DCF0A SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__global_intr_t_agg_sts_dd3dcf0a::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*agg_sts*/   );
        end
    endfunction

    function void hmac_reg__global_intr_t_agg_sts_dd3dcf0a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__GLOBAL_INTR_T_AGG_STS_E6399B4A SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__global_intr_t_agg_sts_e6399b4a::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*agg_sts*/   );
        end
    endfunction

    function void hmac_reg__global_intr_t_agg_sts_e6399b4a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__ERROR_INTR_T_ERROR2_STS_B1CF2205_ERROR3_STS_74A35378_KEY_MODE_ERROR_STS_F2304C86_KEY_ZERO_ERROR_STS_64A18183 SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__error_intr_t_error2_sts_b1cf2205_error3_sts_74a35378_key_mode_error_sts_f2304c86_key_zero_error_sts_64a18183::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_mode_error_sts_bit_cg[bt]) this.key_mode_error_sts_bit_cg[bt].sample(data[0 + bt]);
            foreach(key_zero_error_sts_bit_cg[bt]) this.key_zero_error_sts_bit_cg[bt].sample(data[1 + bt]);
            foreach(error2_sts_bit_cg[bt]) this.error2_sts_bit_cg[bt].sample(data[2 + bt]);
            foreach(error3_sts_bit_cg[bt]) this.error3_sts_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*key_mode_error_sts*/  ,  data[1:1]/*key_zero_error_sts*/  ,  data[2:2]/*error2_sts*/  ,  data[3:3]/*error3_sts*/   );
        end
    endfunction

    function void hmac_reg__error_intr_t_error2_sts_b1cf2205_error3_sts_74a35378_key_mode_error_sts_f2304c86_key_zero_error_sts_64a18183::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_mode_error_sts_bit_cg[bt]) this.key_mode_error_sts_bit_cg[bt].sample(key_mode_error_sts.get_mirrored_value() >> bt);
            foreach(key_zero_error_sts_bit_cg[bt]) this.key_zero_error_sts_bit_cg[bt].sample(key_zero_error_sts.get_mirrored_value() >> bt);
            foreach(error2_sts_bit_cg[bt]) this.error2_sts_bit_cg[bt].sample(error2_sts.get_mirrored_value() >> bt);
            foreach(error3_sts_bit_cg[bt]) this.error3_sts_bit_cg[bt].sample(error3_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( key_mode_error_sts.get_mirrored_value()  ,  key_zero_error_sts.get_mirrored_value()  ,  error2_sts.get_mirrored_value()  ,  error3_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__notif_intr_t_notif_cmd_done_sts_1c68637e::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_sts_bit_cg[bt]) this.notif_cmd_done_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_done_sts*/   );
        end
    endfunction

    function void hmac_reg__notif_intr_t_notif_cmd_done_sts_1c68637e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_sts_bit_cg[bt]) this.notif_cmd_done_sts_bit_cg[bt].sample(notif_cmd_done_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__ERROR_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__error_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_mode_error_trig_bit_cg[bt]) this.key_mode_error_trig_bit_cg[bt].sample(data[0 + bt]);
            foreach(key_zero_error_trig_bit_cg[bt]) this.key_zero_error_trig_bit_cg[bt].sample(data[1 + bt]);
            foreach(error2_trig_bit_cg[bt]) this.error2_trig_bit_cg[bt].sample(data[2 + bt]);
            foreach(error3_trig_bit_cg[bt]) this.error3_trig_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*key_mode_error_trig*/  ,  data[1:1]/*key_zero_error_trig*/  ,  data[2:2]/*error2_trig*/  ,  data[3:3]/*error3_trig*/   );
        end
    endfunction

    function void hmac_reg__error_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_mode_error_trig_bit_cg[bt]) this.key_mode_error_trig_bit_cg[bt].sample(key_mode_error_trig.get_mirrored_value() >> bt);
            foreach(key_zero_error_trig_bit_cg[bt]) this.key_zero_error_trig_bit_cg[bt].sample(key_zero_error_trig.get_mirrored_value() >> bt);
            foreach(error2_trig_bit_cg[bt]) this.error2_trig_bit_cg[bt].sample(error2_trig.get_mirrored_value() >> bt);
            foreach(error3_trig_bit_cg[bt]) this.error3_trig_bit_cg[bt].sample(error3_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( key_mode_error_trig.get_mirrored_value()  ,  key_zero_error_trig.get_mirrored_value()  ,  error2_trig.get_mirrored_value()  ,  error3_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__NOTIF_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__notif_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_trig_bit_cg[bt]) this.notif_cmd_done_trig_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_done_trig*/   );
        end
    endfunction

    function void hmac_reg__notif_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_trig_bit_cg[bt]) this.notif_cmd_done_trig_bit_cg[bt].sample(notif_cmd_done_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_B8D41777 SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_t_cnt_b8d41777::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac_reg__intr_count_t_cnt_b8d41777::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_55FC66D7 SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_t_cnt_55fc66d7::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac_reg__intr_count_t_cnt_55fc66d7::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_D8AF96FF SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_t_cnt_d8af96ff::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac_reg__intr_count_t_cnt_d8af96ff::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_9BD7F809 SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_t_cnt_9bd7f809::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac_reg__intr_count_t_cnt_9bd7f809::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_BE67D6D5 SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_t_cnt_be67d6d5::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac_reg__intr_count_t_cnt_be67d6d5::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_14F62453 SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_incr_t_pulse_14f62453::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac_reg__intr_count_incr_t_pulse_14f62453::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_080329B7 SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_incr_t_pulse_080329b7::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac_reg__intr_count_incr_t_pulse_080329b7::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_87B45FE7 SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_incr_t_pulse_87b45fe7::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac_reg__intr_count_incr_t_pulse_87b45fe7::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_C1689EE6 SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_incr_t_pulse_c1689ee6::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac_reg__intr_count_incr_t_pulse_c1689ee6::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_6173128E SAMPLE FUNCTIONS -----------------------*/
    function void hmac_reg__intr_count_incr_t_pulse_6173128e::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac_reg__intr_count_incr_t_pulse_6173128e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

`endif