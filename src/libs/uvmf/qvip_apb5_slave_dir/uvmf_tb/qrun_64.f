export QVIP_APB5_SLAVE_DIR_NAME=$(pwd)/../uvmf

qrun -f qvip_apb5_slave_test_filelist.f \
+incdir+${QUESTA_MVC_HOME}/questa_mvc_src/sv \
../uvmf/hdl_qvip_apb5_slave.sv \
../uvmf/hvl_qvip_apb5_slave.sv \
-64 \
-debug \
-designfile design.bin \
-c \
-mvchome ${QUESTA_MVC_HOME} \
+nowarnTSCALE -t 1ns \
-do "run -all; quit" \
+UVM_TESTNAME=qvip_apb5_slave_test_base \
+SEQ=qvip_apb5_slave_vseq_base \
-qwavedb=+signal+transaction+class+uvm_schematic
