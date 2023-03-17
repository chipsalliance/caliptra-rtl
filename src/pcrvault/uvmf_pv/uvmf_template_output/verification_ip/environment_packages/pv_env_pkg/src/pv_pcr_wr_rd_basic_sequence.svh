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
// DESCRIPTION: Simple PV write/read sequence via reg model adapter
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class pv_pcr_wr_rd_basic_sequence #(
    type CONFIG_T
) extends pv_env_sequence_base #(.CONFIG_T(CONFIG_T));

    `uvm_object_param_utils(pv_pcr_wr_rd_basic_sequence #(CONFIG_T));

    typedef pv_rst_poweron_sequence pv_rst_agent_poweron_sequence_t;
    pv_rst_agent_poweron_sequence_t pv_rst_agent_poweron_seq;

    function new(string name = "");
        super.new(name);
        pv_rst_agent_poweron_seq = pv_rst_agent_poweron_sequence_t::type_id::create("pv_rst_agent_poweron_seq");
        if(!this.randomize()) `uvm_error("PV PCR WR RD BASIC", "Failed to randomize PV RST poweron seq");
    endfunction

    virtual task body();
        uvm_status_e sts;
        int wr_offset, rd_offset;
        int wr_entry, rd_entry;
        reg [PV_DATA_W-1:0] wr_data, rd_data;
        
        reg_model = configuration.pv_rm;
        
        //Issue reset
        if(configuration.pv_rst_agent_config.sequencer != null)
            pv_rst_agent_poweron_seq.start(configuration.pv_rst_agent_config.sequencer);
        else
            `uvm_error("PV PCR WR RD BASIC", "pv_rst_agent_config.sequencer is null!")
        
        //PCR ENTRY reg writes
        for(wr_entry = 0; wr_entry < PV_NUM_PCR; wr_entry++) begin
            for (wr_offset = 0; wr_offset < PV_NUM_DWORDS; wr_offset++) begin
                std::randomize(wr_data);
                reg_model.pv_reg_rm.PCR_ENTRY[wr_entry][wr_offset].write(sts, wr_data, UVM_FRONTDOOR, reg_model.pv_sha512_write_map, this);
                assert(sts == UVM_IS_OK) else `uvm_error("PV PCR WR RD BASIC", $sformatf("Failed when writing to PCR[%d][%d] entry",wr_entry, wr_offset))
            end
        end
        
        //PCR ENTRY reg reads
        for(rd_entry = 0; rd_entry < PV_NUM_PCR; rd_entry++) begin
            for (rd_offset = 0; rd_offset < PV_NUM_DWORDS; rd_offset++) begin
                reg_model.pv_reg_rm.PCR_ENTRY[rd_entry][rd_offset].read(sts, rd_data, UVM_FRONTDOOR, reg_model.pv_sha512_block_read_map, this);
                assert(sts == UVM_IS_OK) else `uvm_error("PV PCR WR RD BASIC", $sformatf("Failed when reading from PCR[%d][%d] entry",rd_entry, rd_offset))
            end
        end
    endtask


endclass