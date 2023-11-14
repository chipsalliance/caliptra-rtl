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
// Description:
//

#include "systemc.h"
#include "Interfaces.h"
#include "../../hmac_core.h"
#include "hmac_tests.h"
#include "../top.h"
#include "../sha_algo_masked.h"

int sc_main(int argc, char **argv) {
  top top1("top1");
  hmac_tests tests("tests");


   Blocking<block> hmac_msg("hmac_msg");
   Blocking<sc_biguint<KEY_WIDTH>> tag("tag");

  top1.top_hmac(hmac_msg);
  top1.top_tag(tag);

  tests.hmac_msg(hmac_msg);
  tests.tag(tag);
  

  sc_start();
  return 0;
}
