// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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
#include <stdlib.h>

#include <iostream>
#include <string>
#include <utility>

#include "Vspi_host_tb.h"
#include "verilated.h"
#include "verilated_fst_c.h"

vluint64_t main_time = 0;

double sc_time_stamp() { return main_time; }

int main(int argc, char** argv) {
  std::cout << "\nVerilatorTB: Start of sim\n" << std::endl;

  Verilated::commandArgs(argc, argv);

  Vspi_host_tb* tb = new Vspi_host_tb;

  // init trace dump
  VerilatedFstC* tfp = NULL;

#if VM_TRACE
  Verilated::traceEverOn(true);
  tfp = new VerilatedFstC;
  tb->trace(tfp, 24);
  tfp->open("sim.vcd");
#endif
  // Simulate
  while (!Verilated::gotFinish()) {
#if VM_TRACE
    tfp->dump(main_time);
#endif
    main_time += 5;
    tb->clk_tb = !tb->clk_tb;
    tb->eval();
  }

#if VM_TRACE
  tfp->close();
#endif

  std::cout << "\nVerilatorTB: End of sim" << std::endl;
  exit(EXIT_SUCCESS);
}
