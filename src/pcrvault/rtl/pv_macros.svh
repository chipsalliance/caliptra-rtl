// SPDX-License-Identifier: Apache-2.0PV_MACROS
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
`ifndef PV_MACROS
`define PV_MACROS



`define PV_WRITE_CTRL_REG2STRUCT(struct_name, ctrl_reg_name)\
assign struct_name.rsvd = '0;\
assign struct_name.write_dest_vld[0] = hwif_out.``ctrl_reg_name.hmac_key_dest_valid.value;\
assign struct_name.write_dest_vld[1] = hwif_out.``ctrl_reg_name.hmac_block_dest_valid.value;\
assign struct_name.write_dest_vld[2] = hwif_out.``ctrl_reg_name.sha_block_dest_valid.value;\
assign struct_name.write_dest_vld[3] = hwif_out.``ctrl_reg_name.ecc_pkey_dest_valid.value;\
assign struct_name.write_dest_vld[4] = hwif_out.``ctrl_reg_name.ecc_seed_dest_valid.value;\
assign struct_name.write_dest_vld[5] = hwif_out.``ctrl_reg_name.ecc_msg_dest_valid.value;\
assign struct_name.entry_is_pv = hwif_out.``ctrl_reg_name.entry_is_pv.value;\
assign struct_name.write_entry = hwif_out.``ctrl_reg_name.write_entry.value;\
assign struct_name.write_en = hwif_out.``ctrl_reg_name.write_en.value;

`define PV_READ_CTRL_REG2STRUCT(struct_name, ctrl_reg_name)\
assign struct_name.rsvd = '0;\
assign struct_name.entry_data_size = hwif_out.``ctrl_reg_name.entry_data_size.value;\
assign struct_name.entry_is_pv = hwif_out.``ctrl_reg_name.entry_is_pv.value;\
assign struct_name.read_entry = hwif_out.``ctrl_reg_name.read_entry.value;\
assign struct_name.read_en = hwif_out.``ctrl_reg_name.read_en.value;

`endif


