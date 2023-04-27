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
// DESCRIPTION: Simple KV write/read sequence that writes random data
// to all entries and all dwords in order and then reads from them in order
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class kv_key_wr_rd_basic_sequence #(
    type CONFIG_T
) extends kv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(kv_key_wr_rd_basic_sequence #(CONFIG_T));

    typedef kv_rst_poweron_sequence kv_rst_agent_poweron_sequence_t;
    kv_rst_agent_poweron_sequence_t kv_rst_agent_poweron_seq;

    function new(string name = "");
        super.new(name);
        kv_rst_agent_poweron_seq = kv_rst_agent_poweron_sequence_t::type_id::create("kv_rst_agent_poweron_seq");
        //assert(this.randomize()) else `uvm_error("KV KEY WR RD BASIC", "Failed to randomize KV RST poweron seq");
        if(!this.randomize()) `uvm_error("KV KEY WR RD BASIC", "Failed to randomize KV RST poweron seq");
    endfunction

    virtual task body();
        uvm_status_e sts;
        int offset;
        int entry;
        reg [KV_DATA_W-1:0] wr_data, rd_data;
        
        reg_model = configuration.kv_rm;
        
        //Issue reset
        if(configuration.kv_rst_agent_config.sequencer != null)
            kv_rst_agent_poweron_seq.start(configuration.kv_rst_agent_config.sequencer);
        else
            `uvm_error("KV KEY WR RD BASIC", "kv_rst_agent_config.sequencer is null!")
        
        //KEY ENTRY reg writes
        for(entry = 0; entry < KV_NUM_KEYS; entry++) begin
            //reg_model.kv_reg_rm.KEY_CTRL[entry].predict('h00003F00);
            for (offset = 0; offset < KV_NUM_DWORDS; offset++) begin
                std::randomize(wr_data);
                reg_model.kv_reg_rm.KEY_ENTRY[entry][offset].write(sts, wr_data, UVM_FRONTDOOR, reg_model.kv_hmac_write_map, this);
                assert(sts == UVM_IS_OK) else `uvm_error("KV KEY WR RD BASIC", $sformatf("Failed when writing to KEY[%d][%d] entry",entry, offset))
            end
        end
        
        //KEY ENTRY reg reads
        for(entry = 0; entry < KV_NUM_KEYS; entry++) begin
            for (offset = 0; offset < KV_NUM_DWORDS; offset++) begin
                reg_model.kv_reg_rm.KEY_ENTRY[entry][offset].read(sts, rd_data, UVM_FRONTDOOR, reg_model.kv_hmac_key_read_map, this);
                assert(sts == UVM_IS_OK) else `uvm_error("KV KEY WR RD BASIC", $sformatf("Failed when reading from KEY[%d][%d] entry",entry, offset))
            end
        end
    endtask


endclass