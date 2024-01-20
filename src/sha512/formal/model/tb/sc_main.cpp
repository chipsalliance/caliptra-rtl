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
