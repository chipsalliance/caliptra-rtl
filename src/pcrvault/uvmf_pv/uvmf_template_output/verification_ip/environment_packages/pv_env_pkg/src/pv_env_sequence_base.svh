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
// DESCRIPTION: This file contains environment level sequences that will
//    be reused from block to top level simulations.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class pv_env_sequence_base #( 
      type CONFIG_T
      ) extends uvmf_virtual_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( pv_env_sequence_base #(
                           CONFIG_T
                           ) );

  // Handle to the environments register model
// This handle needs to be set before use.
  pv_reg_model_top  reg_model;

// This pv_env_sequence_base contains a handle to a pv_env_configuration object 
// named configuration.  This configuration variable contains a handle to each 
// sequencer within each agent within this environment and any sub-environments.
// The configuration object handle is automatically assigned in the pre_body in the
// base class of this sequence.  The configuration handle is retrieved from the
// virtual sequencer that this sequence is started on.
// Available sequencer handles within the environment configuration:

  // Initiator agent sequencers in pv_environment:
    // configuration.pv_rst_agent_config.sequencer
    // configuration.pv_sha512_write_agent_config.sequencer
    // configuration.pv_sha512_block_read_agent_config.sequencer

  // Responder agent sequencers in pv_environment:


    typedef pv_rst_random_sequence pv_rst_agent_random_sequence_t;
    pv_rst_agent_random_sequence_t pv_rst_agent_rand_seq;

    typedef pv_write_random_sequence pv_sha512_write_agent_random_sequence_t;
    pv_sha512_write_agent_random_sequence_t pv_sha512_write_agent_rand_seq;

    typedef pv_read_random_sequence pv_sha512_block_read_agent_random_sequence_t;
    pv_sha512_block_read_agent_random_sequence_t pv_sha512_block_read_agent_rand_seq;




  // pragma uvmf custom class_item_additional begin
  function bit sha_write_permitted(int entry);
`ifdef CALIPTRA_MODE_SUBSYSTEM
    return entry != PV_PCR_CUR && entry != PV_PCR_JRN;
`else
    return 1'b1;
`endif
  endfunction

  task write_pcr_word(int entry, int offset, logic [PV_DATA_W-1:0] data,
                      int unsigned beats = 1);
    pv_write_pcr_entry_sequence seq;
    seq = pv_write_pcr_entry_sequence#()::type_id::create("directed_write_seq");
    seq.directed = 1;
    seq.directed_write_entry = PV_ENTRY_ADDR_W'(entry);
    seq.directed_write_offset = PV_ENTRY_SIZE_WIDTH'(offset);
    seq.directed_write_data = data;
    seq.beats = beats;
    seq.start(configuration.pv_sha512_write_agent_config.sequencer);
  endtask

  task select_pcr_word(int entry, int offset);
    pv_read_sequence_base seq;
    seq = pv_read_sequence_base#()::type_id::create("directed_read_seq");
    seq.req.read_entry = PV_ENTRY_ADDR_W'(entry);
    seq.req.read_offset = PV_ENTRY_SIZE_WIDTH'(offset);
    seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);
  endtask

  // No stimulus or sampling calls: inspect the selected hardware read response.
  task check_pcr_pins(int entry, int offset, logic [PV_DATA_W-1:0] expected);
    pv_read_t selection;
    pv_rd_resp_t response, expected_response;
    selection = pv_read_t'(configuration.pv_sha512_block_read_agent_config.monitor_bfm.pv_read_i);
    response = pv_rd_resp_t'(configuration.pv_sha512_block_read_agent_config.monitor_bfm.pv_rd_resp_i);
    expected_response.read_data = expected;
    expected_response.error = 0;
    expected_response.last = (offset == PV_NUM_DWORDS-1);
    if (selection !== {PV_ENTRY_ADDR_W'(entry), PV_ENTRY_SIZE_WIDTH'(offset)} ||
        response !== expected_response)
      `uvm_error("PV_PIN_READ", $sformatf(
        "PCR%0d word%0d: selection=%h response=%h expected=%h",
        entry, offset, selection, response, expected_response))
  endtask

  // Check actual pins as well as frontdoor data. Read drivers only return the
  // selection on req, not read_data/error/last.
  task check_pcr_word(int entry, int offset, logic [PV_DATA_W-1:0] expected);
    uvm_status_e sts;
    uvm_reg_data_t data;
    select_pcr_word(entry, offset);
    configuration.pv_sha512_block_read_agent_config.wait_for_num_clocks(3);
    @(negedge configuration.pv_sha512_block_read_agent_config.monitor_bfm.clk_i);
    check_pcr_pins(entry, offset, expected);
    reg_model.pv_reg_rm.PCR_ENTRY[entry][offset].read(
      sts, data, UVM_FRONTDOOR, reg_model.pv_AHB_map, this);
    if (sts != UVM_IS_OK || data !== uvm_reg_data_t'(expected))
      `uvm_error("PV_AHB_READ", $sformatf(
        "PCR%0d word%0d: status=%s data=%h expected=%h",
        entry, offset, sts.name(), data, expected))
  endtask

  task check_sha_request(int entry, int offset, logic [PV_DATA_W-1:0] data);
    pv_write_t actual, expected;
    pv_wr_resp_t response;
    expected.write_en = 1;
    expected.write_entry = PV_ENTRY_ADDR_W'(entry);
    expected.write_offset = PV_ENTRY_SIZE_WIDTH'(offset);
    expected.write_data = data;
    actual = pv_write_t'(configuration.pv_sha512_write_agent_config.monitor_bfm.pv_write_i);
    response = pv_wr_resp_t'(configuration.pv_sha512_write_agent_config.monitor_bfm.pv_wr_resp_i);
    // error is always zero, including SS PCR4/5 DROP; it is NOT acceptance.
    if (actual !== expected || response.error !== 1'b0)
      `uvm_error("PV_RAW_WRITE", $sformatf(
        "Raw request=%h expected=%h response=%h", actual, expected, response))
  endtask
  // pragma uvmf custom class_item_additional end
  
  function new(string name = "" );
    super.new(name);
    pv_rst_agent_rand_seq = pv_rst_agent_random_sequence_t::type_id::create("pv_rst_agent_rand_seq");
    pv_sha512_write_agent_rand_seq = pv_sha512_write_agent_random_sequence_t::type_id::create("pv_sha512_write_agent_rand_seq");
    pv_sha512_block_read_agent_rand_seq = pv_sha512_block_read_agent_random_sequence_t::type_id::create("pv_sha512_block_read_agent_rand_seq");


  endfunction

  virtual task body();

    if ( configuration.pv_rst_agent_config.sequencer != null )
       repeat (25) pv_rst_agent_rand_seq.start(configuration.pv_rst_agent_config.sequencer);
    if ( configuration.pv_sha512_write_agent_config.sequencer != null )
       repeat (25) pv_sha512_write_agent_rand_seq.start(configuration.pv_sha512_write_agent_config.sequencer);
    if ( configuration.pv_sha512_block_read_agent_config.sequencer != null )
       repeat (25) pv_sha512_block_read_agent_rand_seq.start(configuration.pv_sha512_block_read_agent_config.sequencer);


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
