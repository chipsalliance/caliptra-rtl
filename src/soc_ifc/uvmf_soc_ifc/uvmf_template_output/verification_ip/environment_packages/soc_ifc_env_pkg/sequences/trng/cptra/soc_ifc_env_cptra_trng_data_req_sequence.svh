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

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: TRNG REQ sequence to request TRNG data from external 
//              source and receive data from the external source
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_cptra_trng_data_req_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));

  `uvm_object_utils( soc_ifc_env_cptra_trng_data_req_sequence )

  int sts_rsp_count;
  uvm_status_e reg_sts;
  rand bit trng_req_data; 

  extern virtual task soc_ifc_ext_trng_req_data(input trng_req_data);
  extern virtual task soc_ifc_ext_trng_data_wr_done_check_status(output bit data_wr_done);
  extern virtual task soc_ifc_ext_trng_data_wr_done_poll_status();
  extern virtual task soc_ifc_ext_trng_clear_req();

  constraint trng_req { trng_req_data == 1; }

  function new(string name = "");
    super.new(name);

  endfunction

  virtual task pre_body();
    super.pre_body();
    reg_model = configuration.soc_ifc_rm;

    if (cptra_status_agent_rsp_seq == null)
      `uvm_fatal("TRNG_REQ_SEQ", "TRNG REQ Sequence expected a handle to the cptra status agent responder sequence (from bench-level sequence) but got null")
  
  endtask

  virtual task body();

    op_sts_e op_sts;
    sts_rsp_count = 0;

    fork 
      forever begin
        @(cptra_status_agent_rsp_seq.new_rsp) sts_rsp_count++;
      end
    join_none

    `uvm_info("TRNG_REQ_SEQ", $sformatf("Initiating TRNG REQ sequence to SOC"), UVM_MEDIUM)

    soc_ifc_ext_trng_req_data(trng_req_data);
    soc_ifc_ext_trng_data_wr_done_poll_status();
    soc_ifc_ext_trng_clear_req();

  endtask

endclass

task soc_ifc_env_cptra_trng_data_req_sequence::soc_ifc_ext_trng_req_data(input trng_req_data);
  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.write(reg_sts, uvm_reg_data_t'(trng_req_data) << reg_model.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.DATA_REQ.get_lsb_pos(), UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  if (reg_sts != UVM_IS_OK)
    `uvm_error("TRNG_REQ_SEQ", "Register access failed to write TRNG_STATUS register")
endtask

task soc_ifc_env_cptra_trng_data_req_sequence::soc_ifc_ext_trng_data_wr_done_check_status(output bit data_wr_done);
  uvm_reg_data_t reg_data;
  reg_model.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.read(reg_sts, reg_data, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
  if (reg_sts != UVM_IS_OK) begin
     `uvm_error("TRNG_REQ_SEQ", "Register access failed (CPTRA_TRNG_STATUS)")
  end
  else begin
    data_wr_done = reg_data[reg_model.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.DATA_WR_DONE.get_lsb_pos()];
  end
endtask

task soc_ifc_env_cptra_trng_data_req_sequence::soc_ifc_ext_trng_data_wr_done_poll_status();
  bit data_wr_done;

  soc_ifc_ext_trng_data_wr_done_check_status(data_wr_done);
  while (data_wr_done == 1'b0) begin
    configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(200);
    soc_ifc_ext_trng_data_wr_done_check_status(data_wr_done);
  end
endtask


task soc_ifc_env_cptra_trng_data_req_sequence::soc_ifc_ext_trng_clear_req();
    uvm_reg_data_t mask;
    mask = uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.DATA_REQ    .get_lsb_pos() |
           uvm_reg_data_t'(1) << reg_model.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.DATA_WR_DONE.get_lsb_pos();
    reg_model.soc_ifc_reg_rm.CPTRA_TRNG_STATUS.write(reg_sts, mask, UVM_FRONTDOOR, reg_model.soc_ifc_AHB_map, this);
    if (reg_sts != UVM_IS_OK)
        `uvm_error("TRNG_REQ_SEQ", "Register access failed to write TRNG_STATUS register")
endtask
