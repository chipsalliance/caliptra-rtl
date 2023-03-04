export QVIP_AHB_LITE_SLAVE_DIR_NAME=$(pwd)/../uvmf

qrun -f qvip_ahb_lite_slave_test_filelist.f \
+incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv \
../uvmf/hdl_qvip_ahb_lite_slave.sv \
../uvmf/hvl_qvip_ahb_lite_slave.sv \
-debug \
-designfile design.bin \
-c \
-mvchome ${QUESTA_MVC_HOME} \
+nowarnTSCALE -t 1ns \
-do "run -all; quit" \
+UVM_TESTNAME=qvip_ahb_lite_slave_test_base \
+SEQ=qvip_ahb_lite_slave_example_vseq \
-qwavedb=+signal+transaction+class+uvm_schematic
