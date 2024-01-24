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
//

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







