${QUESTA_MVC_HOME}/include/questa_mvc_svapi.sv
+incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv +define+MAP_PROT_ATTR ${QUESTA_MVC_HOME}/questa_mvc_src/sv/mvc_pkg.sv
+incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv +incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv/apb3 ${QUESTA_MVC_HOME}/questa_mvc_src/sv/apb3/mgc_apb3_v1_0_pkg.sv
+incdir+../config_policies ../config_policies/qvip_apb5_slave_params_pkg.sv
qvip_apb5_slave_pkg.sv
+incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv/apb3/modules ${QUESTA_MVC_HOME}/questa_mvc_src/sv/apb3/modules/apb5_master.sv
default_clk_gen.sv
default_reset_gen.sv
hdl_qvip_apb5_slave.sv
hvl_qvip_apb5_slave.sv
-debug
-designfile design.bin
-c
-mvchome ${QUESTA_MVC_HOME}
+nowarnTSCALE -t 1ns
-do "run -all; quit"
+UVM_TESTNAME=qvip_apb5_slave_test_base
+SEQ=qvip_apb5_slave_vseq_base
-qwavedb=+signal+transaction+class+uvm_schematic
