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

#ifndef HMAC_H_
#define HMAC_H_

#include "systemc.h"
#include "Interfaces.h"
#include <iostream>
#include <array>
#include <iomanip>
#include <string>

using namespace std;

#define MSG_WIDTH 1024 // b bits
#define PAD_WIDTH 640
#define DIGEST_WIDTH 512
#define KEY_WIDTH 384 // n bits
#define MASK_WIDTH 512

const sc_biguint<MSG_WIDTH> IPAD = sc_biguint<MSG_WIDTH>("0x3636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636");
const sc_biguint<MSG_WIDTH> OPAD = "0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c";
const sc_biguint<PAD_WIDTH> FINAL_PAD = "0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000580";
const sc_biguint<PAD_WIDTH> garbage_vector = "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000";

enum state
{
    state_IPAD,
    state_OPAD,
    state_HMAC
};

struct sha_block
{
    sc_biguint<MSG_WIDTH> block_msg;
    bool init;
    bool next;
    sc_biguint<74> lfsr_rnd;
};

struct sha_splitter
{
    sha_block sha1;
    sha_block sha2;
};

struct block
{
    sc_biguint<KEY_WIDTH> key;
    sc_biguint<MSG_WIDTH> block_msg;
    bool init, next;
};

sc_biguint<MSG_WIDTH> key_ipadded(sc_biguint<KEY_WIDTH> key)
{
    return (static_cast<sc_biguint<MSG_WIDTH>>((static_cast<sc_biguint<MSG_WIDTH>>(key << (PAD_WIDTH))) ^ IPAD));
}

sc_biguint<MSG_WIDTH> key_opadded(sc_biguint<KEY_WIDTH> key)
{
    return (static_cast<sc_biguint<MSG_WIDTH>>(static_cast<sc_biguint<MSG_WIDTH>>(key << (PAD_WIDTH))) ^ OPAD);
}

sc_biguint<MSG_WIDTH> hmac_padded(sc_biguint<KEY_WIDTH> hmac_digest)
{
    return (static_cast<sc_biguint<MSG_WIDTH>>(static_cast<sc_biguint<MSG_WIDTH>>(hmac_digest << (PAD_WIDTH))) | FINAL_PAD);
}

SC_MODULE(HMAC)
{
public:
    SC_CTOR(HMAC)
    {

        SC_THREAD(fsm);
    }

#ifndef  LUBIS
     blocking_out<sha_splitter> sha_msg_1 , sha_msg_2;
#else
    master_out<sha_splitter> sha_msg /*, sha_msg_2*/;
#endif

    blocking_in<sc_biguint<DIGEST_WIDTH>> H1_digest, H2_digest, H1_setup_digest;
    blocking_in<block> hmac_msg;

#ifndef  LUBIS
    blocking_out<sc_biguint<KEY_WIDTH>> tag;
   
#else
         master_out<sc_biguint<KEY_WIDTH>> tag;
#endif

private:
    sc_biguint<MSG_WIDTH> sha_msg_input_ipad;
    sc_biguint<DIGEST_WIDTH> sha_digest_out_ipad, sha_digest_out_ipad_2, sha_digest_out_opad;
    sc_biguint<MSG_WIDTH> S1, S2;
    sc_biguint<KEY_WIDTH> temp;
    bool first_round;
    block hmac;
    sc_biguint<MSG_WIDTH> hmac_blk_msg;
    sha_splitter sha_inst;
    sc_biguint<KEY_WIDTH> key_i;
    sc_biguint<MSG_WIDTH> block_msg_i;
    bool init_i, next_i;

    void fsm()
    {

        while (true)
        {

            sha_msg_input_ipad = hmac_padded(sc_biguint<KEY_WIDTH>(0));

            hmac_msg->read(hmac, "idle");
            cout<<"INIT"<<endl;
            if (hmac.init)
            {

                sha_inst.sha1.block_msg = key_ipadded(hmac.key);
                sha_inst.sha1.init = true;
                sha_inst.sha1.next = false;
                sha_inst.sha2.block_msg = key_opadded(hmac.key);
                sha_inst.sha2.init = false;
                sha_inst.sha2.next = false;
#ifndef LUBIS
               sha_msg_1->write(sha_inst);
#else

                sha_msg->master_write(sha_inst);
#endif
                cout<<"IPAD"<<endl;
                H1_setup_digest->read(sha_digest_out_ipad, "ctrl_ipad");
            }

            sha_inst.sha2.block_msg = key_opadded(hmac.key);
            sha_inst.sha2.next = false;
            sha_inst.sha2.init = true;
            sha_inst.sha1.block_msg = hmac.block_msg;
            sha_inst.sha1.init = false;
            sha_inst.sha1.next = true;
#ifndef LUBIS
            sha_msg_1->write(sha_inst);
#else
            sha_msg->master_write(sha_inst);
#endif
                cout<<"OPAD"<<endl;

            H1_digest->read(sha_digest_out_ipad, "ctrl_opad");

            temp = static_cast<sc_biguint<KEY_WIDTH>>(sha_digest_out_ipad >> 128);

            sha_msg_input_ipad = hmac_padded(temp);

            sha_inst.sha1.block_msg = key_ipadded(hmac.key);
            sha_inst.sha1.init = false;
            sha_inst.sha1.next = false;
            sha_inst.sha2.block_msg = sha_msg_input_ipad;
            sha_inst.sha2.init = false;
            sha_inst.sha2.next = true;


#ifndef LUBIS
        sha_msg_2->write(sha_inst);
#else
        sha_msg->master_write(sha_inst);
#endif
            cout<<"ctrl_hmac"<<endl;

            H2_digest->read(sha_digest_out_opad, "ctrl_hmac");
            insert_state("done_tag");

            cout<<"done"<<endl;

#ifndef LUBIS
        tag->write((sha_digest_out_opad >> 128));
#else
        tag->master_write((sha_digest_out_opad >> 128));
#endif    
        }
    }
};

#endif
