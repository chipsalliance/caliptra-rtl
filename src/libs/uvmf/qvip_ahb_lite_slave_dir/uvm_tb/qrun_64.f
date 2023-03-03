${QUESTA_MVC_HOME}/include/questa_mvc_svapi.sv
+incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv +define+MAP_PROT_ATTR ${QUESTA_MVC_HOME}/questa_mvc_src/sv/mvc_pkg.sv
+incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv +incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv/ahb ${QUESTA_MVC_HOME}/questa_mvc_src/sv/ahb/mgc_ahb_v2_0_pkg.sv
+incdir+../config_policies ../config_policies/qvip_ahb_lite_slave_params_pkg.sv
qvip_ahb_lite_slave_pkg.sv
+incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv/ahb/modules ${QUESTA_MVC_HOME}/questa_mvc_src/sv/ahb/modules/ahb_lite_slave.sv
default_clk_gen.sv
default_reset_gen.sv
hdl_qvip_ahb_lite_slave.sv
hvl_qvip_ahb_lite_slave.sv
-64
-debug
-designfile design.bin
-c
-mvchome ${QUESTA_MVC_HOME}
+nowarnTSCALE -t 1ns
-do "run -all; quit"
+UVM_TESTNAME=qvip_ahb_lite_slave_test_base
+SEQ=qvip_ahb_lite_slave_example_vseq
-qwavedb=+signal+transaction+class+uvm_schematic
