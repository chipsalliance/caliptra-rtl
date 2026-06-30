// SPDX-License-Identifier: Apache-2.0
// 
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

#include <stdint.h>

uint32_t __xorshift32_state = (unsigned) MY_RANDOM_SEED;

void xorshift32_init(uint32_t seed) {
    __xorshift32_state = seed;
}

uint32_t xorshift32(void) {
    __xorshift32_state ^= __xorshift32_state << 13;
    __xorshift32_state ^= __xorshift32_state >> 17;
    __xorshift32_state ^= __xorshift32_state << 5;
    return __xorshift32_state;
}