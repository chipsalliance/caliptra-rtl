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
`ifndef CALIPTRA_KV_MACROS
`define CALIPTRA_KV_MACROS



`define CALIPTRA_KV_WRITE_CTRL_REG2STRUCT(struct_name, ctrl_reg_name, hwif_name = hwif_out)\
assign struct_name.rsvd = '0;\
assign struct_name.write_dest_vld[0] = ``hwif_name.``ctrl_reg_name.hmac_key_dest_valid.value;\
assign struct_name.write_dest_vld[1] = ``hwif_name.``ctrl_reg_name.hmac_block_dest_valid.value;\
assign struct_name.write_dest_vld[2] = ``hwif_name.``ctrl_reg_name.mldsa_seed_dest_valid.value;\
assign struct_name.write_dest_vld[3] = ``hwif_name.``ctrl_reg_name.ecc_pkey_dest_valid.value;\
assign struct_name.write_dest_vld[4] = ``hwif_name.``ctrl_reg_name.ecc_seed_dest_valid.value;\
assign struct_name.write_dest_vld[5] = ``hwif_name.``ctrl_reg_name.aes_key_dest_valid.value;\
assign struct_name.write_dest_vld[6] = ``hwif_name.``ctrl_reg_name.mlkem_seed_dest_valid.value;\
assign struct_name.write_dest_vld[7] = ``hwif_name.``ctrl_reg_name.mlkem_msg_dest_valid.value;\
assign struct_name.write_dest_vld[8] = ``hwif_name.``ctrl_reg_name.dma_data_dest_valid.value;\
assign struct_name.write_entry = ``hwif_name.``ctrl_reg_name.write_entry.value;\
assign struct_name.write_en = ``hwif_name.``ctrl_reg_name.write_en.value;

`define CALIPTRA_KV_READ_CTRL_REG2STRUCT(struct_name, ctrl_reg_name, hwif_name = hwif_out)\
assign struct_name.rsvd = '0;\
assign struct_name.pcr_hash_extend = ``hwif_name.``ctrl_reg_name.pcr_hash_extend.value;\
assign struct_name.read_entry = ``hwif_name.``ctrl_reg_name.read_entry.value;\
assign struct_name.read_en = ``hwif_name.``ctrl_reg_name.read_en.value;

`define CALIPTRA_KV_READ_STATUS_ASSIGN(sig_prefix, hwif_name = hwif_in)\
assign ``hwif_name.``sig_prefix``_rd_status.ERROR.next = ``sig_prefix``_error;\
assign ``hwif_name.``sig_prefix``_rd_status.READY.next = ``sig_prefix``_ready;\
assign ``hwif_name.``sig_prefix``_rd_status.VALID.hwset = ``sig_prefix``_done;\
assign ``hwif_name.``sig_prefix``_rd_status.VALID.hwclr = ``sig_prefix``_read_ctrl_reg.read_en;\
assign ``hwif_name.``sig_prefix``_rd_ctrl.read_en.hwclr = ~``sig_prefix``_ready;

`define CALIPTRA_KV_WRITE_STATUS_ASSIGN(sig_prefix, hwif_name = hwif_in)\
assign ``hwif_name.``sig_prefix``_wr_status.ERROR.next = ``sig_prefix``_error;\
assign ``hwif_name.``sig_prefix``_wr_status.READY.next = ``sig_prefix``_ready;\
assign ``hwif_name.``sig_prefix``_wr_status.VALID.hwset = ``sig_prefix``_done;\
assign ``hwif_name.``sig_prefix``_wr_status.VALID.hwclr = ``sig_prefix``_write_ctrl_reg.write_en;\
assign ``hwif_name.``sig_prefix``_wr_ctrl.write_en.hwclr = ~``sig_prefix``_ready;

`endif


