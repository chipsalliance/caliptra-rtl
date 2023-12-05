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

#ifndef HMAC_SHA_
#define HMAC_SHA_

#include "systemc.h"
#include "Interfaces.h"
#include <iostream>
#include <array>
#include <iomanip>
#include <random>
#include <string>
#include "../hmac_core.h"

using namespace std;

#define MSG_WIDTH 1024 // b bits
#define PAD_WIDTH 640
#define DIGEST_WIDTH 512
#define KEY_WIDTH 384 // n bits
#define MASK_WIDTH 512

SC_MODULE(hmac_sha)
{
public:
    SC_CTOR(hmac_sha)
    {
        SC_THREAD(fsm);
    }

    blocking_in<sha_splitter> sha_msg_split_1 ,sha_msg_split_2;
    blocking_out<sc_biguint<DIGEST_WIDTH>> hmac_setup_digest, hmac_1_digest, hmac_2_digest;

    blocking_out<sha_block> h_sha_msg_1, h_sha_msg_2;
    blocking_in<sc_biguint<DIGEST_WIDTH>> sha_1_digest, sha_2_digest;

private:
    sha_splitter chunk1, chunk2, chunk3;
    sha_block shablock1, shablock2;
    sc_biguint<1024> MSG_raw_1, MSG_raw_2, block_msg_reg;
    sc_biguint<2048> msg_comb;
    sc_biguint<104000> MSG_padded, shift_pad;
    sc_biguint<DIGEST_WIDTH> sha_digest_out_ipad, sha_digest_out_ipad_2, sha_digest_out_opad;
    sc_uint<32> MSG_Length;
    sc_biguint<384> expected_result;
    sc_biguint<DIGEST_WIDTH> garabage_digest;
    bool init_reg, next_reg;

    int num = 1;
    int zero_pad_len, MSG_chnks, i, j;

    void fsm()
    {       
            std::random_device seed;
            std::default_random_engine generator(seed());
            std::uniform_int_distribution<long long unsigned> distribution(0,0xFFFFFFFFFFFFFFFF);
        while (true)
        {

            // cout << "sha_hmac_read_start" << endl;
            sha_msg_split_1->read(chunk1, "ipad_state1");
            if (chunk1.sha1.init)
            {
                shablock1.block_msg = chunk1.sha1.block_msg;
                shablock1.init = chunk1.sha1.init;

                shablock1.next = chunk1.sha1.next;
                shablock2.block_msg = chunk1.sha1.block_msg;
                shablock2.init = chunk1.sha2.init;
                shablock2.next = chunk1.sha2.next;

                h_sha_msg_1->write(shablock1, "send_sha1_key");

                sha_1_digest->read(garabage_digest, "sha1_digest_out");
                hmac_setup_digest->write(garabage_digest, "read_garbage_digest");
                sha_msg_split_1->read(chunk2, "ipad_state2");

                MSG_Length = 1024;
                MSG_chnks = 2;
                // cout << "sha_hmac_read_block" << endl;

                MSG_raw_1 = chunk2.sha1.block_msg;

                init_reg = chunk2.sha2.init;
                block_msg_reg = chunk2.sha2.block_msg;
                next_reg = chunk2.sha2.next;

                shablock1.init = chunk2.sha1.init;
                shablock1.next = chunk2.sha1.next;
            }
            else
            {
                MSG_Length = 1024;
                MSG_chnks = 2;
                // cout << "sha_hmac_read_block" << endl;

                MSG_raw_1 = chunk1.sha1.block_msg;

                init_reg = chunk1.sha2.init;
                block_msg_reg = chunk1.sha2.block_msg;
                next_reg = chunk1.sha2.next;

                shablock1.init = chunk1.sha1.init;
                shablock1.next = chunk1.sha1.next;
            }

            MSG_padded = static_cast<sc_biguint<104000>>(static_cast<sc_biguint<104000>>(MSG_raw_1 << (1024)) + (static_cast<sc_biguint<104000>>(8) << static_cast<sc_biguint<104000>>(1020)) + static_cast<sc_biguint<104000>>(2048));
            //cout << "MSG_padded::" << MSG_padded << endl;
            for (i = 0; i < MSG_chnks; ++i)
            {   
                shablock1.lfsr_rnd= static_cast<sc_biguint<74>>(distribution(generator))*sc_biguint<74>(1024) + static_cast<sc_biguint<74>>(distribution(generator)); 
                shablock1.block_msg = static_cast<sc_biguint<1024>>(MSG_padded >> (1024 * (MSG_chnks - 1)));
                if (i > 0)
                {
                    shablock1.next = chunk2.sha1.next;
                }

                h_sha_msg_1->write(shablock1, "send_ipad_msg");
                MSG_padded = static_cast<sc_biguint<104000>>(MSG_padded << 1024);
                shablock1.init = chunk2.sha1.init;

                sha_1_digest->read(sha_digest_out_ipad_2, "sha1_digest_out");
            }
            hmac_1_digest->write(sha_digest_out_ipad_2, "shaop_IPAD_DIGEST_HMAC");
            //////////////////////////////////////

            MSG_Length = 1024;
            MSG_chnks = 2;
            // cout << "sha_hmac_read_digest" << endl;

            sha_msg_split_2->read(chunk3, "ipad_state2");
            shablock1.block_msg = chunk3.sha1.block_msg;
            shablock1.init = chunk3.sha1.init;
            shablock1.next = chunk3.sha1.next;
            MSG_raw_2 = chunk3.sha2.block_msg;

            MSG_padded = ((static_cast<sc_biguint<2048>>(block_msg_reg)) << 1024) | (MSG_raw_2);
            // cout << "MSG_padded_sha2::" << MSG_padded << endl;

            shablock2.init = init_reg;
            shablock2.next = next_reg;

            for (j = 0; j < MSG_chnks; j++)
            {
                shablock2.lfsr_rnd= static_cast<sc_biguint<74>>(distribution(generator))*sc_biguint<74>(1024) + static_cast<sc_biguint<74>>(distribution(generator));
                shablock2.block_msg = static_cast<sc_biguint<1024>>(MSG_padded >> (1024 * (MSG_chnks - 1)));
                if (j > 0)
                {
                    shablock2.next = chunk3.sha1.next;
                }
                h_sha_msg_2->write(shablock2, "send_ipad_msg");
                MSG_padded = static_cast<sc_biguint<104000>>(MSG_padded << 1024);
                shablock2.init = chunk3.sha1.init;
                sha_2_digest->read(sha_digest_out_opad, "sha1_digest_out");
            }
            hmac_2_digest->write(sha_digest_out_opad, "shaop_IPAD_DIGEST_HMAC");

            chunk1.sha1.init = chunk3.sha1.init;
        }
    }
};

#endif