#include "systemc.h"
#include "../Interfaces/Interfaces.h"
#include "../sha512.h"
#include "tb.h"


int sc_main(int argc, char **argv) {
  Blocking<SHA_Args> in_channel("in_channel");
  MasterSlave<sc_biguint<512>> out_channel("out_channel");

  testbench tb("tb");
  tb.in_testdata(in_channel);
  tb.out_testdata(out_channel);
  
  SHA512 dut("dut");
  dut.SHA_Input(in_channel);
  dut.out(out_channel);



  sc_start();
  return 0;
}
