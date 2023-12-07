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
#include "systemc.h"
#include "string.h"
#include "Interfaces.h" 
using    namespace std;
#define  NUM_ROUNDS  80

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

sc_biguint<64> Ch(sc_biguint<64> a, sc_biguint<64> b, sc_biguint<64> c)  {
    return static_cast<sc_biguint<64>>((a & b) ^ (~a & c));
}

sc_biguint<64> Maj(sc_biguint<64> x, sc_biguint<64> y, sc_biguint<64> z)  {
    return static_cast<sc_biguint<64>>((x & y) ^ (x & z) ^ (y & z));
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

sc_biguint<64> T1(sc_biguint<64> e, sc_biguint<64> f, sc_biguint<64> g, sc_biguint<64> h, sc_biguint<64> k, sc_biguint<64> w)  {  
    return static_cast<sc_biguint<64>>(h + sigma1(e) + Ch(e, f, g) + k + w);
}

sc_biguint<64> T2(sc_biguint<64> a, sc_biguint<64> b, sc_biguint<64> c)  { 
    return static_cast<sc_biguint<64>>(sigma0(a) + Maj(a, b, c));
}
sc_biguint<64> compute_e(sc_biguint<64> d,sc_biguint<64> e, sc_biguint<64> f, sc_biguint<64> g, sc_biguint<64> h, sc_biguint<64> k, sc_biguint<64> w)  {  
    return static_cast<sc_biguint<64>>(d+ h + sigma1(e) + Ch(e, f, g) + k + w);
}
sc_biguint<64> compute_a(sc_biguint<64> e, sc_biguint<64> f, sc_biguint<64> g, sc_biguint<64> h, sc_biguint<64> k, sc_biguint<64> w,sc_biguint<64> a, sc_biguint<64> b, sc_biguint<64> c)  {
    return static_cast<sc_biguint<64>>((static_cast<sc_biguint<64>>(h + sigma1(e) + Ch(e, f, g) + k + w))+(static_cast<sc_biguint<64>>(sigma0(a) + Maj(a, b, c))));
}

sc_biguint<64> compute_w(sc_biguint<64> w14, sc_biguint<64> w9, sc_biguint<64> w1, sc_biguint<64> w0) {
    return static_cast<sc_biguint<64>>(delta1(w14) + w9 + delta0(w1) + w0);
}

sc_biguint<512> compute_dig (sc_biguint<512> dig,sc_biguint<64> h7, sc_biguint<64> h6, sc_biguint<64> h5, sc_biguint<64> h4,sc_biguint<64> h3,sc_biguint<64> h2, sc_biguint<64> h1, sc_biguint<64> h0){
            dig += static_cast<sc_biguint<512>> (h6 << sc_biguint<64>(448));
            dig = static_cast<sc_biguint<512>> (dig >> sc_biguint<512>(64));
            dig += static_cast<sc_biguint<512>> (h6 << sc_biguint<64>(448));
            dig = static_cast<sc_biguint<512>> (dig >> sc_biguint<512>(64));
            dig += static_cast<sc_biguint<512>> (h5 << sc_biguint<64>(448));
            dig = static_cast<sc_biguint<512>> (dig >> sc_biguint<512>(64));
            dig += static_cast<sc_biguint<512>> (h4 << sc_biguint<64>(448));
            dig = static_cast<sc_biguint<512>> (dig >> sc_biguint<512>(64));
            dig += static_cast<sc_biguint<512>> (h3 << sc_biguint<64>(448));
            dig = static_cast<sc_biguint<512>> (dig >> sc_biguint<512>(64));
            dig += static_cast<sc_biguint<512>> (h2 << sc_biguint<64>(448));
            dig = static_cast<sc_biguint<512>> (dig >> sc_biguint<512>(64));
            dig += static_cast<sc_biguint<512>> (h1 << sc_biguint<64>(448));
            dig = static_cast<sc_biguint<512>> (dig >> sc_biguint<512>(64));
            dig += static_cast<sc_biguint<512>> (h0 << sc_biguint<64>(448));
            
            return(dig);
        
}
struct SHA_Args{
    sc_biguint<1024> in;
    int SHA_Mode;
    bool init;
    bool next;
    bool zeroize; 
};
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
      sc_biguint<64>(0x5fcb6fab3ad6faec), sc_biguint<64>(0x6c44198c4a475817)};;


SC_MODULE(SHA512) {
   
    blocking_in <SHA_Args> SHA_Input;
    master_out <sc_biguint<512>> out; 

    array   <sc_biguint<64>, 16> W;
    array   <sc_biguint<64>, 8>  H;
 
    sc_biguint<64> t1 = sc_biguint<64> (0), t2 = sc_biguint<64> (0), 
                    a = sc_biguint<64> (0),  b = sc_biguint<64> (0), 
                    c = sc_biguint<64> (0),  d = sc_biguint<64> (0),
                    e = sc_biguint<64> (0),  f = sc_biguint<64> (0), 
                    g = sc_biguint<64> (0),  h = sc_biguint<64> (0), 
                    w = sc_biguint<64> (0),  k = sc_biguint<64> (0);
    sc_biguint<64> tmp_w;  

    sc_biguint<1024> block_in; 
    sc_biguint<1024> block_copy; 
    sc_biguint<512> MSG_digest;

    SHA_Args SHA_in;
    int SHA_Mode_in;
    bool init, next, success, zeroize;

    int i, j, m=0;

    void fsm();

    SC_CTOR(SHA512){
        SC_THREAD(fsm);
    }  
};

void SHA512::fsm(){

while(true){
    
        SHA_Input->read(SHA_in, "IDLE");

        block_in = SHA_in.in;
        SHA_Mode_in = SHA_in.SHA_Mode;
        init = SHA_in.init;
        next = SHA_in.next;
        zeroize = SHA_in.zeroize; 
    
        if (init){
            switch (SHA_Mode_in){
                case 224:
                    H ={sc_biguint<64>(0x8c3d37c819544da2), sc_biguint<64>(0x73e1996689dcd4d6),\
                        sc_biguint<64>(0x1dfab7ae32ff9c82), sc_biguint<64>(0x679dd514582f9fcf),\
                        sc_biguint<64>(0x0f6d2b697bd44da8), sc_biguint<64>(0x77e36f7304c48942),\
                        sc_biguint<64>(0x3f9d85a86a1d36c8), sc_biguint<64>(0x1112e6ad91d692a1)};
                    break;
                case 256:
                    H ={sc_biguint<64>(0x22312194fc2bf72c), sc_biguint<64>(0x9f555fa3c84c64c2),\
                        sc_biguint<64>(0x2393b86b6f53b151), sc_biguint<64>(0x963877195940eabd),\
                        sc_biguint<64>(0x96283ee2a88effe3), sc_biguint<64>(0xbe5e1e2553863992),\
                        sc_biguint<64>(0x2b0199fc2c85b8aa), sc_biguint<64>(0x0eb72ddc81c52ca2)};
                    break;
                /*case 384:
                    H ={sc_biguint<64>(0xcbbb9d5dc1059ed8), sc_biguint<64>(0x629a292a367cd507),\
                        sc_biguint<64>(0x9159015a3070dd17), sc_biguint<64>(0x152fecd8f70e5939),\
                        sc_biguint<64>(0x67332667ffc00b31), sc_biguint<64>(0x8eb44a8768581511),\
                        sc_biguint<64>(0xdb0c2e0d64f98fa7), sc_biguint<64>(0x47b5481dbefa4fa4)};
                    break;*/
                case 512:
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

            t1 = sc_biguint<64> (0); t2 = sc_biguint<64> (0); 
            a  = sc_biguint<64> (0); b  = sc_biguint<64> (0); 
            c  = sc_biguint<64> (0); d  = sc_biguint<64> (0);
            e  = sc_biguint<64> (0); f  = sc_biguint<64> (0); 
            g  = sc_biguint<64> (0); h  = sc_biguint<64> (0); 
            w  = sc_biguint<64> (0); k  = sc_biguint<64> (0);
            W  = {sc_biguint<64>(0)};
        }

        block_copy = block_in;  

        for (j=0; j<16; ++j) {    
            W[15-j] = slicer(block_copy, j);
        };
        
        a = H[0]; b = H[1];c = H[2]; d = H[3]; 
        e = H[4]; f = H[5];g = H[6]; h = H[7];
        
        for (i=0; i<NUM_ROUNDS; ++i) { 
            insert_state("SHA_Rounds");
            k = K[i];
            if (i < 16){
                w = W[i];   
            }   
            else {   
                tmp_w = compute_w(W[14],W[9],W[1],W[0]);
                for (j=0; j<15; ++j) { 
                    W[j] = W[(j+1)];
                }
                W[15] = tmp_w;
                w = tmp_w;                 
            }

            t1 = T1(e, f, g, h, K[i],w);  
            t2 = T2(a, b, c);
            h = g;
            g = f;
            f = e;
            e = (d + t1);
            d = c; 
            c = b;
            b = a;
            a = (t1 + t2);        
        } 
        insert_state("DONE"); 

        H[0] = (H[0] + a) ;
        H[1] = (H[1] + b) ;
        H[2] = (H[2] + c) ;
        H[3] = (H[3] + d) ;
        H[4] = (H[4] + e) ;
        H[5] = (H[5] + f) ;
        H[6] = (H[6] + g) ;
        H[7] = (H[7] + h) ;                 
        
         MSG_digest = static_cast<sc_biguint<512>> (H[7] << (sc_biguint<64>(448)));
        for (j=6; j > -1; --j) {         
            MSG_digest = static_cast<sc_biguint<512>> (MSG_digest >> sc_biguint<512>(64));
            MSG_digest += static_cast<sc_biguint<512>> (H[j] << sc_biguint<64>(448));
        }
        
        out->master_write(static_cast<sc_biguint<512>> (MSG_digest)); 
    }

};
#endif
