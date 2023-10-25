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

#ifndef SHA
#define SHA

#include <array>
#include <random>
#include "systemc.h"
#include "string.h"
#include "Interfaces.h" 
#include "../hmac_core.h"
using    namespace std;

#define  NUM_ROUNDS  80
#define  SHA512_RNDs 9
const sc_biguint<74> LFSR_INIT_SEED = sc_biguint<74>(0xA79D0EC11E389277);

std::random_device seed;
std::default_random_engine generator(seed());
std::uniform_int_distribution<long long unsigned> distribution(0,0xFFFFFFFFFFFFFFFF);

//0x079D0EC11E389277); // a random value, copied from RTL: 
//BYME: check latest versin of code, Luref, functions23A
//ASK: I don't want some stuff in luref
//BYME: changed fv_constraints to fix block_msg
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------

/* struct sha_block
{
    sc_biguint<MSG_WIDTH> block_msg;
    bool init;
    bool next;
    sc_biguint<74> lfsr_rnd;
}; */
struct masked_reg_t {
    sc_biguint<64>  masked, random;
};

//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------

 sc_biguint<64> slicer(sc_biguint<1024> block, int index) {
    switch (index){
        case 0:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 0));
            break;
        case 1:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 1));
            break;
        case 2:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 2));
            break;
        case 3:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 3));
            break;
        case 4:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 4));
            break;
        case 5:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 5));
            break;
        case 6:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 6));
            break;
        case 7:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 7));
            break;
        case 8:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 8));
            break;
        case 9:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 9));
            break;
        case 10:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 10));
            break;
        case 11:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 11));
            break;
        case 12:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 12));
            break;
        case 13:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 13));
            break;
        case 14:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 14));
            break;
        case 15:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 15));
            break;
        default:
            return static_cast<sc_biguint<64>> (block >> sc_biguint<1024>(64 * 15));
            break;
    }  
}

sc_biguint<512> concati(sc_biguint<512> MSG_digest, array   <sc_biguint<64>, 8> H, int j)  {
    MSG_digest = static_cast<sc_biguint<512>> (H[7] << (sc_biguint<64>(448)));
    for (j=6; j > -1; --j) {         
        MSG_digest = static_cast<sc_biguint<512>> (MSG_digest >> sc_biguint<512>(64));
        MSG_digest += static_cast<sc_biguint<512>> (H[j] << sc_biguint<64>(448));
    };
    return MSG_digest;
}

sc_biguint<64> shr6(sc_biguint<64> n)  {  
    return static_cast<sc_biguint<64>>(n >> sc_biguint<64>(6));
}

sc_biguint<64> shr7(sc_biguint<64> n)  {  
    return static_cast<sc_biguint<64>>(n >> sc_biguint<64>(7));
}

sc_biguint<64> rotr1(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(1)))  | (n << (sc_biguint<64>(63))));
}

sc_biguint<64> rotr8(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(8)))  | (n << (sc_biguint<64>(56))));
}

sc_biguint<64> rotr14(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(14))) | (n << (sc_biguint<64>(50))));
}

sc_biguint<64> rotr18(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(18))) | (n << (sc_biguint<64>(46))));
}

sc_biguint<64> rotr19(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(19))) | (n << (sc_biguint<64>(45))));
}

sc_biguint<64> rotr28(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(28))) | (n << (sc_biguint<64>(36))));
}

sc_biguint<64> rotr34(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(34))) | (n << (sc_biguint<64>(30))));
}

sc_biguint<64> rotr39(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(39))) | (n << (sc_biguint<64>(25))));
}

sc_biguint<64> rotr41(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(41))) | (n << (sc_biguint<64>(23))));
}

sc_biguint<64> rotr61(sc_biguint<64> n)  {
    return static_cast<sc_biguint<64>>((n >> (sc_biguint<64>(61))) | (n << (sc_biguint<64>(3))));
}

sc_biguint<64> sigma0(sc_biguint<64> x){
    return static_cast<sc_biguint<64>> (rotr28(x) ^ rotr34(x) ^ rotr39(x));
}

sc_biguint<64> sigma1(sc_biguint<64> x)  {
    return static_cast<sc_biguint<64>> (rotr14(x) ^ rotr18(x) ^ rotr41(x));
}

sc_biguint<64> delta0(sc_biguint<64> x)  { 
    return static_cast<sc_biguint<64>> (rotr1(x) ^ rotr8(x) ^ shr7(x));
}

sc_biguint<64> delta1(sc_biguint<64> x)  { 
    return static_cast<sc_biguint<64>> (rotr19(x) ^ rotr61(x) ^ shr6(x));
}

sc_biguint<64> masked_and(sc_biguint<64> x_masked, sc_biguint<64> x_random, sc_biguint<64> y_masked, sc_biguint<64> y_random)  { 
    return (~y_masked & ((~y_random & x_random) | (y_random & x_masked))) | (y_masked & ((y_random & x_random) | (~y_random & x_masked))); //x & y;
}

sc_biguint<64> masked_Maj(sc_biguint<64> a_masked, sc_biguint<64> a_random, sc_biguint<64> b_masked, sc_biguint<64> b_random, sc_biguint<64> c_masked, sc_biguint<64> c_random)  { 
    return masked_and(a_masked, a_random, b_masked, b_random) ^ masked_and(a_masked, a_random, c_masked, c_random) ^ masked_and(b_masked, b_random, c_masked, c_random);
}

sc_biguint<64> masked_Ch_m(sc_biguint<64> e_masked, sc_biguint<64> e_random, sc_biguint<64> f_masked, sc_biguint<64> f_random, sc_biguint<64> g_masked, sc_biguint<64> g_random)  { 
    return masked_and(e_masked, e_random, f_masked, f_random) ^ masked_and(g_masked, g_random, ~e_masked, e_random);
}

sc_biguint<64> masked_Ch_r(sc_biguint<64> e_masked, sc_biguint<64> e_random, sc_biguint<64> f_masked, sc_biguint<64> f_random, sc_biguint<64> g_masked, sc_biguint<64> g_random)  { 
    return e_random ^ g_random;
}

sc_biguint<64> B2A_conv(sc_biguint<64> x_masked, sc_biguint<64> x_random, bool q, bool masked_carry, sc_biguint<128> x_prime, sc_biguint<64> mask, int j)  {  // convert x_masked = x ^ rnd to x_prime = x + rand
    // masked_carry[j] = c[j] ^ qs
    mask = sc_biguint<64>(0x01);
    x_prime = sc_biguint<128>(0);
    masked_carry = q;  //used this initial value to avoid the separate case of 0

    for (j = 0; j < 64; ++j) { //BYME: change next line
        x_prime += ((x_masked & mask) == mask) != masked_carry != q ? sc_biguint<128>(16) * sc_biguint<128>(0x01000000000000000) : sc_biguint<128>(0);
        masked_carry = (!((x_masked & mask) == mask) and (((x_random & mask) == mask) != q)) or (((x_masked & mask) == mask) and masked_carry);       
        
        x_prime = x_prime >> sc_biguint<128>(1);
        mask = mask << sc_biguint<64>(1);
    } 

    return static_cast<sc_biguint<64>>(x_prime);//x_prime
}

sc_biguint<64> A2B_conv(sc_biguint<64> x_masked, sc_biguint<64> x_random, bool q, bool masked_carry, sc_biguint<128> x_m, sc_biguint<64> mask, int j)  {  // convert x_prime = x + rand to x_masked = x ^ rnd
    // masked_carry[j] = c[j] ^ q
    mask = sc_biguint<64>(0x01);
    x_m = static_cast<sc_biguint<128>>((x_masked & mask) << (sc_biguint<128>(64)));
    masked_carry = (not((x_masked & mask) == mask) and ((x_random & mask) == mask)) != q;//used this initial value to avoid separate case of 0

    for (j = 1; j < 64; ++j) {
        mask = mask << sc_biguint<64>(1); 

        x_m = (x_m >> 1);//BYME: change next line
        x_m += ((x_masked & mask) == mask) != masked_carry != q ? sc_biguint<128>(16) * sc_biguint<128>(0x01000000000000000) : sc_biguint<128>(0);

        masked_carry = ((((x_masked & mask) == mask) != ((x_random & mask) == mask)) and (((x_random & mask) == mask) != q)) or ((!((x_masked & mask) == mask) != ((x_random & mask) == mask)) and masked_carry);                   

    }
    x_m = (x_m >> 1);

    
    return static_cast<sc_biguint<64>>(x_m);//x_m
}

sc_biguint<64> T1_m(sc_biguint<64> e_masked, sc_biguint<64> e_random, sc_biguint<64> f_masked, sc_biguint<64> f_random, sc_biguint<64> g_masked, sc_biguint<64> g_random, sc_biguint<64> h_masked, sc_biguint<64> h_random, sc_biguint<64> k, sc_biguint<64> w_masked, sc_biguint<64> w_random, bool masked_carry, sc_biguint<128> x_prime, sc_biguint<64> mask, bool q_masking_rnd_0, bool q_masking_rnd_1, bool q_masking_rnd_2, bool q_masking_rnd_3, bool q_masking_rnd_4, int j)  {          

    return static_cast<sc_biguint<64>>(B2A_conv(h_masked, h_random,      q_masking_rnd_0, masked_carry, x_prime, mask, j) +
           B2A_conv(sigma1(e_masked), sigma1(e_random),                  q_masking_rnd_1, masked_carry, x_prime, mask, j)+ 
           B2A_conv(masked_Ch_m(e_masked, e_random, f_masked, f_random, g_masked, g_random), e_random ^ g_random, q_masking_rnd_2, masked_carry, x_prime, mask, j) +
           B2A_conv(k, sc_biguint<64>(0x0),                              q_masking_rnd_3, masked_carry, x_prime, mask, j) + 
           B2A_conv(w_masked, w_random,                                  q_masking_rnd_4, masked_carry, x_prime, mask, j));
}

sc_biguint<64> T1_r(sc_biguint<64> e_random, sc_biguint<64> g_random, sc_biguint<64> h_random, sc_biguint<64> w_random)  {      
    return static_cast<sc_biguint<64>>(h_random + sigma1(e_random) + (e_random ^ g_random) + w_random);
}

sc_biguint<64> T2_m(sc_biguint<64> a_masked, sc_biguint<64> a_random, sc_biguint<64> b_masked, sc_biguint<64> b_random, sc_biguint<64> c_masked, sc_biguint<64> c_random, bool masked_carry, sc_biguint<128> x_prime, sc_biguint<64> mask, bool q_masking_rnd_5, bool q_masking_rnd_6, int j)  { 
    return static_cast<sc_biguint<64>>(B2A_conv(sigma0(a_masked), sigma0(a_random), q_masking_rnd_5, masked_carry, x_prime, mask, j) +
           B2A_conv(masked_Maj(a_masked, a_random, b_masked, b_random, c_masked, c_random), b_random, q_masking_rnd_6, masked_carry, x_prime, mask, j));
} 

sc_biguint<64> T2_r(sc_biguint<64> a_random, sc_biguint<64> b_random)  { 
    return static_cast<sc_biguint<64>>(sigma0(a_random) + b_random);
} 

sc_biguint<74> lfsr(sc_biguint<74> a)  { 
    return static_cast<sc_biguint<74>>((a * 2) + (a[73] ^ a[72] ^ a[58] ^ a[57]));
}

//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
const array   <sc_biguint<64>, 80> K =
     {sc_biguint<64>(0x428a2f98d728ae22), sc_biguint<64>(0x7137449123ef65cd), sc_biguint<64>(0xb5c0fbcfec4d3b2f),\
      sc_biguint<64>(0xe9b5dba58189dbbc), sc_biguint<64>(0x3956c25bf348b538), sc_biguint<64>(0x59f111f1b605d019),\
      sc_biguint<64>(0x923f82a4af194f9b), sc_biguint<64>(0xab1c5ed5da6d8118), sc_biguint<64>(0xd807aa98a3030242),\
      sc_biguint<64>(0x12835b0145706fbe), sc_biguint<64>(0x243185be4ee4b28c), sc_biguint<64>(0x550c7dc3d5ffb4e2),\
      sc_biguint<64>(0x72be5d74f27b896f), sc_biguint<64>(0x80deb1fe3b1696b1), sc_biguint<64>(0x9bdc06a725c71235),\
      sc_biguint<64>(0xc19bf174cf692694), sc_biguint<64>(0xe49b69c19ef14ad2), sc_biguint<64>(0xefbe4786384f25e3),\
      sc_biguint<64>(0x0fc19dc68b8cd5b5), sc_biguint<64>(0x240ca1cc77ac9c65), sc_biguint<64>(0x2de92c6f592b0275),\
      sc_biguint<64>(0x4a7484aa6ea6e483), sc_biguint<64>(0x5cb0a9dcbd41fbd4), sc_biguint<64>(0x76f988da831153b5),\
      sc_biguint<64>(0x983e5152ee66dfab), sc_biguint<64>(0xa831c66d2db43210), sc_biguint<64>(0xb00327c898fb213f),\
      sc_biguint<64>(0xbf597fc7beef0ee4), sc_biguint<64>(0xc6e00bf33da88fc2), sc_biguint<64>(0xd5a79147930aa725),\
      sc_biguint<64>(0x06ca6351e003826f), sc_biguint<64>(0x142929670a0e6e70), sc_biguint<64>(0x27b70a8546d22ffc),\
      sc_biguint<64>(0x2e1b21385c26c926), sc_biguint<64>(0x4d2c6dfc5ac42aed), sc_biguint<64>(0x53380d139d95b3df),\
      sc_biguint<64>(0x650a73548baf63de), sc_biguint<64>(0x766a0abb3c77b2a8), sc_biguint<64>(0x81c2c92e47edaee6),\
      sc_biguint<64>(0x92722c851482353b), sc_biguint<64>(0xa2bfe8a14cf10364), sc_biguint<64>(0xa81a664bbc423001),\
      sc_biguint<64>(0xc24b8b70d0f89791), sc_biguint<64>(0xc76c51a30654be30), sc_biguint<64>(0xd192e819d6ef5218),\
      sc_biguint<64>(0xd69906245565a910), sc_biguint<64>(0xf40e35855771202a), sc_biguint<64>(0x106aa07032bbd1b8),\
      sc_biguint<64>(0x19a4c116b8d2d0c8), sc_biguint<64>(0x1e376c085141ab53), sc_biguint<64>(0x2748774cdf8eeb99),\
      sc_biguint<64>(0x34b0bcb5e19b48a8), sc_biguint<64>(0x391c0cb3c5c95a63), sc_biguint<64>(0x4ed8aa4ae3418acb),\
      sc_biguint<64>(0x5b9cca4f7763e373), sc_biguint<64>(0x682e6ff3d6b2b8a3), sc_biguint<64>(0x748f82ee5defb2fc),\
      sc_biguint<64>(0x78a5636f43172f60), sc_biguint<64>(0x84c87814a1f0ab72), sc_biguint<64>(0x8cc702081a6439ec),\
      sc_biguint<64>(0x90befffa23631e28), sc_biguint<64>(0xa4506cebde82bde9), sc_biguint<64>(0xbef9a3f7b2c67915),\
      sc_biguint<64>(0xc67178f2e372532b), sc_biguint<64>(0xca273eceea26619c), sc_biguint<64>(0xd186b8c721c0c207),\
      sc_biguint<64>(0xeada7dd6cde0eb1e), sc_biguint<64>(0xf57d4f7fee6ed178), sc_biguint<64>(0x06f067aa72176fba),\
      sc_biguint<64>(0x0a637dc5a2c898a6), sc_biguint<64>(0x113f9804bef90dae), sc_biguint<64>(0x1b710b35131c471b),\
      sc_biguint<64>(0x28db77f523047d84), sc_biguint<64>(0x32caab7b40c72493), sc_biguint<64>(0x3c9ebe0a15c9bebc),\
      sc_biguint<64>(0x431d67c49c100d4c), sc_biguint<64>(0x4cc5d4becb3e42b6), sc_biguint<64>(0x597f299cfc657e2a),\
      sc_biguint<64>(0x5fcb6fab3ad6faec), sc_biguint<64>(0x6c44198c4a475817)};

SC_MODULE(SHA512_masked) {
   
    blocking_in <sha_block> SHA_Input;
    blocking_out <sc_biguint<512>> out; 

    array   <sc_biguint<64>, 16> W;
    array   <sc_biguint<64>, 8>  H;
    array   <sc_biguint<64>, 8> rh_masking_rnd = {sc_biguint<64>(0)};
 
    masked_reg_t   t1 = {sc_biguint<64>(0)}, t2 = {sc_biguint<64>(0)}, 
                    a = {sc_biguint<64>(0)},  b = {sc_biguint<64>(0)}, 
                    c = {sc_biguint<64>(0)},  d = {sc_biguint<64>(0)},
                    e = {sc_biguint<64>(0)},  f = {sc_biguint<64>(0)}, 
                    g = {sc_biguint<64>(0)},  h = {sc_biguint<64>(0)},
                    w_data = {sc_biguint<64>(0)};
    sc_biguint<64>  w = sc_biguint<64> (0),  k = sc_biguint<64> (0);
    sc_biguint<64>  tmp_w;  

    sc_biguint<1024> block_in; 
    sc_biguint<1024> block_copy; 
    sc_biguint<512>  MSG_digest;

    sc_biguint<74> lfsr_rnd;
    //sc_biguint<74> lfsr_rnd = LFSR_INIT_SEED;
    sc_biguint<74> lfsr_rnd_c;

    sha_block SHA_in;
    int SHA_Mode_in;
    bool init_cmd, next_cmd, success, zeroize;

    bool masked_carry; 
    sc_biguint<64> mask = sc_biguint<64>(0x01);;
    sc_biguint<64> rw_masking_rnd;
    array <bool, 10> q_masking_rnd;
    sc_biguint<128> x_prime; 
    sc_biguint<128> x_masked;

    int i, j, m=0, p;

    void fsm();

    SC_CTOR(SHA512_masked){
        SC_THREAD(fsm);
    }  
};

void SHA512_masked::fsm(){

    while(true){
        //lfsr_rnd = LFSR_INIT_SEED;  //BYME: otherwise in reset property would be 0
        SHA_Input->read(SHA_in, "IDLE");

        block_in = SHA_in.block_msg;
        lfsr_rnd = SHA_in.lfsr_rnd;
        SHA_Mode_in = 384;
        init_cmd = SHA_in.init;
        next_cmd = SHA_in.next;
        //zeroize = SHA_in.zeroize; 

        //for (p=0; p<SHA512_RNDs; ++p) { 
        insert_state("CTRL_RND");
        //}; BYME: remove p from luref

        if (init_cmd){
            switch (SHA_Mode_in){
                case 0:
                    H ={sc_biguint<64>(0x8c3d37c819544da2), sc_biguint<64>(0x73e1996689dcd4d6),\
                        sc_biguint<64>(0x1dfab7ae32ff9c82), sc_biguint<64>(0x679dd514582f9fcf),\
                        sc_biguint<64>(0x0f6d2b697bd44da8), sc_biguint<64>(0x77e36f7304c48942),\
                        sc_biguint<64>(0x3f9d85a86a1d36c8), sc_biguint<64>(0x1112e6ad91d692a1)};
                    break;
                case 1:
                    H ={sc_biguint<64>(0x22312194fc2bf72c), sc_biguint<64>(0x9f555fa3c84c64c2),\
                        sc_biguint<64>(0x2393b86b6f53b151), sc_biguint<64>(0x963877195940eabd),\
                        sc_biguint<64>(0x96283ee2a88effe3), sc_biguint<64>(0xbe5e1e2553863992),\
                        sc_biguint<64>(0x2b0199fc2c85b8aa), sc_biguint<64>(0x0eb72ddc81c52ca2)};
                    break;
                /*case 2:
                    H ={sc_biguint<64>(0xcbbb9d5dc1059ed8), sc_biguint<64>(0x629a292a367cd507),\
                        sc_biguint<64>(0x9159015a3070dd17), sc_biguint<64>(0x152fecd8f70e5939),\
                        sc_biguint<64>(0x67332667ffc00b31), sc_biguint<64>(0x8eb44a8768581511),\
                        sc_biguint<64>(0xdb0c2e0d64f98fa7), sc_biguint<64>(0x47b5481dbefa4fa4)};
                    break;*/
                case 3:
                    H ={sc_biguint<64>(0x6a09e667f3bcc908), sc_biguint<64>(0xbb67ae8584caa73b),\
                        sc_biguint<64>(0x3c6ef372fe94f82b), sc_biguint<64>(0xa54ff53a5f1d36f1),\
                        sc_biguint<64>(0x510e527fade682d1), sc_biguint<64>(0x9b05688c2b3e6c1f),\
                        sc_biguint<64>(0x1f83d9abfb41bd6b), sc_biguint<64>(0x5be0cd19137e2179)};
                    break;
                default:
                    H ={sc_biguint<64>(0xcbbb9d5dc1059ed8), sc_biguint<64>(0x629a292a367cd507),\
                        sc_biguint<64>(0x9159015a3070dd17), sc_biguint<64>(0x152fecd8f70e5939),\
                        sc_biguint<64>(0x67332667ffc00b31), sc_biguint<64>(0x8eb44a8768581511),\
                        sc_biguint<64>(0xdb0c2e0d64f98fa7), sc_biguint<64>(0x47b5481dbefa4fa4)};
                    break;
            }
            //     BYME: Wasn't it this way before?
            t1= {sc_biguint<64>(0)}; t2 = {sc_biguint<64>(0)}; 
            a = {sc_biguint<64>(0)};  b = {sc_biguint<64>(0)}; 
            c = {sc_biguint<64>(0)};  d = {sc_biguint<64>(0)};
            e = {sc_biguint<64>(0)};  f = {sc_biguint<64>(0)}; 
            g = {sc_biguint<64>(0)};  h = {sc_biguint<64>(0)};     
            w = sc_biguint<64> (0);   k = sc_biguint<64> (0);
            W = {sc_biguint<64>(0)};
            //lfsr_rnd = LFSR_INIT_SEED;//BYME lfsr_seed;
        }

        for (j=0; j<8; ++j) { //BYME: if (masking_init)rh_masking_rnd[rnd_ctr_reg[2 : 0]] <= lfsr_rnd[63 : 0];
            rh_masking_rnd[j] = lfsr_rnd;
        };  

        //next(block_in);
        //W_schedule(block_in);
        block_copy = block_in;

        for (j=0; j<16; ++j) {    
            W[15-j] = slicer(block_copy, j);
        };

        //copy_digest();           
        a = {H[0] ^ rh_masking_rnd[0], rh_masking_rnd[0]}; b = {H[1] ^ rh_masking_rnd[1], rh_masking_rnd[1]};
        c = {H[2] ^ rh_masking_rnd[2], rh_masking_rnd[2]}; d = {H[3] ^ rh_masking_rnd[3], rh_masking_rnd[3]}; 
        e = {H[4] ^ rh_masking_rnd[4], rh_masking_rnd[4]}; f = {H[5] ^ rh_masking_rnd[5], rh_masking_rnd[5]};
        g = {H[6] ^ rh_masking_rnd[6], rh_masking_rnd[6]}; h = {H[7] ^ rh_masking_rnd[7], rh_masking_rnd[7]};
        
        for (i=0; i<NUM_ROUNDS; ++i) { 
            lfsr_rnd = static_cast<sc_biguint<74>>(distribution(generator))*sc_biguint<74>(1024) + static_cast<sc_biguint<74>>(distribution(generator));
            //std::cout << std::dec << "LFSR_RND in round " << i << " is: " << std::hex << lfsr_rnd  << std::endl; 
            insert_state("SHA_Rounds");
            //sha512_round(i);
            k = K[i];
            //w = next_w(i);
        
            if (i < 16)
                w = W[i];           
            else {   
                tmp_w = delta1(W[14]) + W[9] + delta0(W[1]) + W[0];
                for (j=0; j<15; ++j) { 
                    W[j] = W[(j+1)];
                };
                W[15] = tmp_w;
                w = tmp_w;                   
            };

            rw_masking_rnd = static_cast<sc_biguint<64>>(lfsr_rnd);
            lfsr_rnd_c = lfsr_rnd >> 64;
            for (j=0; j<10; ++j) { 
                q_masking_rnd[j] = ((lfsr_rnd_c) & 0x1) == 1;
                lfsr_rnd_c = lfsr_rnd_c >> 1;
            };
            w_data = {w ^ rw_masking_rnd, rw_masking_rnd};
            t1 = {T1_m(e.masked, e.random, f.masked, f.random, g.masked, g.random, h.masked, h.random, k, w_data.masked, w_data.random, masked_carry, x_prime, mask, q_masking_rnd[0], q_masking_rnd[1], q_masking_rnd[2], q_masking_rnd[3], q_masking_rnd[4], j), T1_r(e.random, g.random, h.random, w_data.random)};
            t2 = {T2_m(a.masked, a.random, b.masked, b.random, c.masked, c.random, masked_carry, x_prime, mask, q_masking_rnd[5], q_masking_rnd[6], j), T2_r(a.random, b.random)};
            h = g;
            g = f;
            f = e;           
            e = {A2B_conv((B2A_conv(d.masked, d.random, q_masking_rnd[7], masked_carry, x_prime, mask, j) + t1.masked), (d.random + t1.random), q_masking_rnd[9], masked_carry, x_masked, mask, j), (d.random + t1.random)};
            d = c; 
            c = b;
            b = a;
            a = {A2B_conv((t1.masked + t2.masked), (t1.random + t2.random), q_masking_rnd[8], masked_carry, x_masked, mask, j), (t1.random + t2.random)};        
            
        };
        insert_state("DONE"); 
        //update_digest(); 
        H[0] = (H[0] + (a.masked ^ a.random)); 
        H[1] = (H[1] + (b.masked ^ b.random)); 
        H[2] = (H[2] + (c.masked ^ c.random)); 
        H[3] = (H[3] + (d.masked ^ d.random)); 
        H[4] = (H[4] + (e.masked ^ e.random)); 
        H[5] = (H[5] + (f.masked ^ f.random)); 
        H[6] = (H[6] + (g.masked ^ g.random)); 
        H[7] = (H[7] + (h.masked ^ h.random));                  
         
        MSG_digest = static_cast<sc_biguint<512>> (H[7] << (sc_biguint<64>(448)));
        for (j=6; j > -1; --j) {         
            MSG_digest = static_cast<sc_biguint<512>> (MSG_digest >> sc_biguint<512>(64));
            MSG_digest += static_cast<sc_biguint<512>> (H[j] << sc_biguint<64>(448));
        };
        //MSG_digest = concati(MSG_digest, H, j); 
        /*   BYME: to comply with rtl
        switch (SHA_Mode_in){
            case 0:
                MSG_digest = static_cast<sc_biguint<512>> (MSG_digest >> sc_biguint<512>(288)); 
                break;
            case 1:
                MSG_digest = static_cast<sc_biguint<512>> (MSG_digest >> sc_biguint<512>(256)); 
                break;
            case 2:
                MSG_digest = static_cast<sc_biguint<512>> (MSG_digest >> sc_biguint<512>(128)); 
                break;
            case 3:
                MSG_digest = static_cast<sc_biguint<512>> (MSG_digest); 
                break;            
            default:
                MSG_digest = static_cast<sc_biguint<512>> (MSG_digest >> sc_biguint<512>(128)); 
                break;
        }*/
        
        out->write(static_cast<sc_biguint<512>> (MSG_digest)); 
        
    //}; 
    
    //out->write(static_cast<sc_biguint<512>> (MSG_digest >> static_cast<sc_biguint<512>>(512-SHA_Mode_in))); 
    }
};
#endif