using namespace std;
#include <array>
#include "systemc.h"
#include "../common/Interfaces.h" 
#include "sha512.h"
#include "tb.h"

int main() {
    // Instantiate the DUT
    // Instantiate the TB
    SHA512 dut("dut");
    testbench tb("tb");

    // Channels & connections
    Blocking<SHA_Args> SHA_in("SHA_in");
    MasterSlave<sc_biguint<512>> hash("hash");

    dut.SHA_Input(SHA_in);
    tb.in_testdata(SHA_in);
    dut.out(hash);
    tb.out_testdata(hash);

    // Start the simulation
    sc_start();
    return 0;
};







