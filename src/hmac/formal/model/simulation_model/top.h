// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
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
#include "Interfaces.h"
#include "../hmac_core.h"
#include "sha_algo_masked.h"
#include "hmac_sha_join.h"

SC_MODULE(top)
{

   HMAC hmc;
   SHA512_masked sha384_1;
   SHA512_masked sha384_2;
   hmac_sha hmacsha;

   blocking_in<block> top_hmac;
   blocking_out<sc_biguint<KEY_WIDTH>> top_tag;

   Blocking<block> hmac_msg;
   Blocking<sc_biguint<KEY_WIDTH>> tag;

   Blocking<sha_splitter> sha_msg_split_1, sha_msg_split_2;
   Blocking<sc_biguint<DIGEST_WIDTH>> H1_setup_digest, hmac_1_digest, hmac_2_digest;
   Blocking<sha_block> h_sha_msg_1, h_sha_msg_2;
   Blocking<sc_biguint<DIGEST_WIDTH>> sha_1_digest, sha_2_digest;

   SC_CTOR(top) : hmc("hmc"),
   sha384_1("sha384_1"),
   sha384_2("sha384_2"),
   hmacsha("hmacsha"),

   top_hmac("top_in"),
   top_tag("top_out"),

   hmac_msg("hmac_msg"),
   tag("tag"),

   sha_msg_split_1("sha_msg_split_1"),
   sha_msg_split_2("sha_msg_split_2"),
   //sha_msg_split_2("sha_msg_split_2"),

   H1_setup_digest("H1_setup_digest"),
   hmac_1_digest("hmac_1_digest"),
   hmac_2_digest("hmac_2_digest"),

   h_sha_msg_1("h_sha_msg_1"),
   h_sha_msg_2("h_sha_msg_2"),
   sha_1_digest("sha_1_digest"),
   sha_2_digest("sha_2_digest")
   {

      hmc.hmac_msg(top_hmac);

      hmc.sha_msg_1(sha_msg_split_1);
      hmacsha.sha_msg_split_1(sha_msg_split_1);

      hmacsha.h_sha_msg_1(h_sha_msg_1);
      sha384_1.SHA_Input(h_sha_msg_1);

      sha384_1.out(sha_1_digest);

      hmacsha.hmac_setup_digest(H1_setup_digest);
      hmc.H1_setup_digest(H1_setup_digest);

      // hmc.sha_msg_2(sha_msg_split_2);
      // hmacsha.sha_msg_split_2(sha_msg_split_2);

      hmacsha.sha_1_digest(sha_1_digest);

      hmacsha.hmac_1_digest(hmac_1_digest);
      hmc.H1_digest(hmac_1_digest);

      hmc.sha_msg_2(sha_msg_split_2);
      hmacsha.sha_msg_split_2(sha_msg_split_2);

      hmacsha.h_sha_msg_2(h_sha_msg_2);
      sha384_2.SHA_Input(h_sha_msg_2);

      sha384_2.out(sha_2_digest);
      hmacsha.sha_2_digest(sha_2_digest);

      hmacsha.hmac_2_digest(hmac_2_digest);
      hmc.H2_digest(hmac_2_digest);

      hmc.tag(top_tag);
   }
};