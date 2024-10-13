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
#include "caliptra_reg.h"

extern int STACK;
void main () {
    // Set stack pointer value pointed in linker script
    __asm__ volatile ("la sp, %0"
                      : /* output */
                      : "i" ((int) &STACK) /* input: */
                      : /* clobbers */);

    int idx = 0;
    char* stdout = (char*)CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0;
    char* message = "============================\nHello World from Caliptra!\n> Executing Recovery Image <\n============================\n";
    char toprint = message[idx];
    while (toprint != 0) { *stdout = toprint; toprint = message[idx++]; }
    *stdout = 0xff;
}
