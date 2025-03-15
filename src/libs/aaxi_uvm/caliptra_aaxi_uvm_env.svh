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

`ifndef caliptra_aaxi_uvm_env_sv
`define caliptra_aaxi_uvm_env_sv

/* 
    UVM env class in which AXI master, slave and interconnect are instantiated
*/

class caliptra_aaxi_uvm_env extends uvm_env;

    protected int unsigned num_masters= AAXI_INTC_MASTER_CNT;
    protected int unsigned num_slaves= AAXI_INTC_SLAVE_CNT;
    protected int enable_intc= 0; 	// enable interconnect bfm
    caliptra_aaxi_ports aaxi_ports;

    aaxi_uvm_agent master[];
//    aaxi_uvm_agent slave[];

    aaxi_uvm_agent psv_master[];
//    aaxi_uvm_agent psv_slave[];

    aaxi_uvm_mem         mems[];
    aaxi_uvm_mem_adapter mem_adapters[];

    `uvm_component_utils_begin(caliptra_aaxi_uvm_env)
        `uvm_field_int(num_masters, UVM_ALL_ON)
        `uvm_field_int(num_slaves, UVM_ALL_ON)
        `uvm_field_int(enable_intc, UVM_ALL_ON)
    `uvm_component_utils_end

    // new - constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new


    virtual function void build_phase(uvm_phase phase); 
        string s, s2, mem_s, mem_adp_s, msg_str, mem_str, mem_adp_str;
        super.build();
        void'(uvm_config_db #(caliptra_aaxi_ports)::get(uvm_root::get(), "*", "intf_aaxi_ports", aaxi_ports));

        // Master instantiation
        master = new[num_masters];
        mems = new[num_masters];
        mem_adapters = new[num_masters];
        for(int i = 0; i < num_masters; i++) begin
            $sformat(s, "master[%0d]", i);
            $sformat(s2, "%s.driver", s);
            $sformat(msg_str, " %m %s at %0t", s, $time);
            `uvm_info("AAXI_INF", msg_str, UVM_LOW);
            master[i] = aaxi_uvm_agent::type_id::create(s, this);
            master[i].dev_type = AAXI_MASTER;
            uvm_config_db #(int)::set(this, {s, "*"}, "port_id", i);
            // extract aaxi_uvm_test_base from top to pkg

            uvm_config_db #(virtual aaxi_intf#(.MCB_INPUT(aaxi_pkg::AAXI_MCB_INPUT),.MCB_OUTPUT(aaxi_pkg::AAXI_MCB_OUTPUT),.SCB_INPUT(aaxi_pkg::AAXI_SCB_INPUT),.SCB_OUTPUT(aaxi_pkg::AAXI_SCB_OUTPUT)))::set(this, s2, "ports", aaxi_ports.m_ports_arr[i]);
            $sformat(mem_s, "mems[%0d]", i);
            $sformat(mem_str, " %m %s at %0t", mem_s, $time);
            `uvm_info("AAXI_INF", mem_str, UVM_LOW);
            mems[i] = aaxi_uvm_mem::type_id::create(mem_s, this);
            mems[i].base_addr    = 'h0;
            mems[i].num_location = 4096;
            mems[i].build_phase(phase);
            mems[i].lock_model();

            $sformat(mem_adp_s, "mem_adapters[%0d]", i);
            $sformat(mem_adp_str, " %m %s at %0t", mem_adp_s, $time);
            `uvm_info("AAXI_INF", mem_adp_str, UVM_LOW);
            mem_adapters[i] = aaxi_uvm_mem_adapter::type_id::create(mem_adp_s, this);
        end

`ifdef AVERY_PASSIVE_MASTER
	// Passive master instantiation
        psv_master = new[num_masters];
        for(int i = 0; i < num_masters; i++) begin
            $sformat(s, "psv_master[%0d]", i);
            $sformat(msg_str, " %m %s at %0t", s, $time);
            `uvm_info("AAXI_INF", msg_str, UVM_LOW);
            psv_master[i] = aaxi_uvm_agent::type_id::create(s, this);
            psv_master[i].dev_type = AAXI_MASTER;
            uvm_config_db #(int)::set(this, {s, "*"}, "port_id", i);
        end
`endif


//        // Slave instantiation
//        slave = new[num_slaves];
//        for (int i = 0; i < num_slaves; i++) begin
//            $sformat(s, "slave[%0d]", i);
//            $sformat(s2, "%s.driver", s);
//            $sformat(msg_str, " %m %s at %0t", s, $time);
//            `uvm_info("AAXI_INF", msg_str, UVM_LOW);
//            slave[i] = aaxi_uvm_agent::type_id::create(s, this);
//            slave[i].dev_type = AAXI_SLAVE;
//            uvm_config_int::set(this, {s, "*"}, "port_id", i);
//            // extract aaxi_uvm_test_base from top to pkg
//            uvm_config_db #(virtual aaxi_intf#(.MCB_INPUT(aaxi_pkg::AAXI_MCB_INPUT),.MCB_OUTPUT(aaxi_pkg::AAXI_MCB_OUTPUT),.SCB_INPUT(aaxi_pkg::AAXI_SCB_INPUT),.SCB_OUTPUT(aaxi_pkg::AAXI_SCB_OUTPUT)))::set(this, s2, "ports", aaxi_ports.s_ports_arr[i]);
//        end
//
//`ifdef AVERY_PASSIVE_SLAVE
//	// Passive slave instantiation
//        psv_slave = new[num_slaves];
//        for(int i = 0; i < num_slaves; i++) begin
//            $sformat(s, "psv_slave[%0d]", i);
//            $sformat(msg_str, " %m %s at %0t", s, $time);
//            `uvm_info("AAXI_INF", msg_str, UVM_LOW);
//            psv_slave[i] = aaxi_uvm_agent::type_id::create(s, this);
//            psv_slave[i].dev_type = AAXI_SLAVE;
//            uvm_config_db #(int)::set(this, {s, "*"}, "port_id", i);
//        end
//`endif

    endfunction: build_phase 

    virtual function void connect_phase(uvm_phase phase);
        for(int i = 0; i < num_masters; i++) begin
            mems[i].default_map.set_sequencer(master[i].sequencer, mem_adapters[i]);

        end
    endfunction: connect_phase

endclass

`endif // caliptra_aaxi_uvm_env_sv
