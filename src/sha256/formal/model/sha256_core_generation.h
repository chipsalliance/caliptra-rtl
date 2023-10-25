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

#ifndef SHA256_CORE_H
#define SHA256_CORE_H

#include "systemc.h"
#include "Interfaces.h"
#include <array>
const std::array<uint32_t, 64> K{0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
								 0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
								 0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
								 0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
								 0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
								 0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
								 0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
								 0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
								 0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
								 0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
								 0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
								 0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
								 0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
								 0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
								 0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
								 0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u};

uint32_t rotr(uint32_t x, uint32_t n) 
	{
		return (x >> n) | (x << (32u - n));
	}
	uint32_t choose(uint32_t e, uint32_t f, uint32_t g) 
	{
		return (e & f) ^ (~e & g);
	}
	uint32_t majority(uint32_t a, uint32_t b, uint32_t c) 
	{
		return (a & (b | c)) | (b & c);
	}
	uint32_t sig0(uint32_t x) 
	{
		return rotr(x, 7u) ^ rotr(x, 18u) ^ (x >> 3u);
	}
	uint32_t sig1(uint32_t x) 
	{
		return rotr(x, 17u) ^ rotr(x, 19u) ^ (x >> 10u);
	}
	uint32_t Summ(uint32_t x, uint32_t y, uint32_t z, uint32_t m, uint32_t e) 
	{
		return x + y + z + m + e;
	}
	uint32_t newe(uint32_t x, uint32_t y) 
	{
		return x + y;
	}
	uint32_t newa(uint32_t x, uint32_t y, uint32_t z) 
	{
		return x + y + z;
	}
	uint32_t mult_xor(uint32_t x, uint32_t a, uint32_t b,uint32_t c) {
		return (rotr(x,a)^rotr(x,b)^rotr(x,c));
	}
	uint32_t compute_w(uint32_t m14, uint32_t m9,uint32_t m1, uint32_t m0){
		return (sig1(m14)+m9+sig0(m1)+m0);
	}
SC_MODULE(sha256_core)
{
public:
	uint32_t k_constant;
	uint32_t maj, xorA, ch, xorE, sum, newA, newE, w_temp, w_data;
	std::array<uint32_t, 8> state;

	std::array<uint32_t, 8> m_state;
	std::array<uint32_t, 16> block_dummy;
	std::array<uint32_t, 16> m;
	int i, l, k;
	uint32_t j;

	bool next_dummy, init_transform_dummy, mode_dummy, zeroize_dummy;
	blocking_in<std::array<uint32_t, 16>> w_core;
	shared_in<bool> mode;
	sc_biguint<512> out;

	master_out<std::array<uint32_t, 8>> digest_block;

	shared_in<bool> next_signal, init_signal, zeroize;

	SC_CTOR(sha256_core)
	{
		SC_THREAD(fsm);
	}

	void fsm()
	{

		state[0] = 0x0u;
		state[1] = 0x0u;
		state[2] = 0x0u;
		state[3] = 0x0u;
		state[4] = 0x0u;
		state[5] = 0x0u;
		state[6] = 0x0u;
		state[7] = 0x0u;
		m_state[0] = 0x0u;
		m_state[1] = 0x0u;
		m_state[2] = 0x0u;
		m_state[3] = 0x0u;
		m_state[4] = 0x0u;
		m_state[5] = 0x0u;
		m_state[6] = 0x0u;
		m_state[7] = 0x0u;
		w_data = 0x0u;
		k_constant = 0x0u;
		w_temp = 0x0u;
		i = 0x0u;

		while (true)

		{

			w_core->read(block_dummy, "idle");
			init_signal->get(init_transform_dummy);
			next_signal->get(next_dummy);
			mode->get(mode_dummy);
			zeroize->get(zeroize_dummy);

			if (init_transform_dummy == true)
			{
				
				if(mode_dummy==false){
				 // 224
					m_state[0] = 0xc1059ed8;
					m_state[1] = 0x367cd507;
					m_state[2] = 0x3070dd17;
					m_state[3] = 0xf70e5939;
					m_state[4] = 0xffc00b31;
					m_state[5] = 0x68581511;
					m_state[6] = 0x64f98fa7;
					m_state[7] = 0xbefa4fa4;
					k_constant = 0u;
				}
				else {// 256
					m_state[0] = 0x6a09e667u;
					m_state[1] = 0xbb67ae85u;
					m_state[2] = 0x3c6ef372u;
					m_state[3] = 0xa54ff53au;
					m_state[4] = 0x510e527fu;
					m_state[5] = 0x9b05688cu;
					m_state[6] = 0x1f83d9abu;
					m_state[7] = 0x5be0cd19u;
					k_constant = 0u;
				}
				
				
			}
			for (k = 0u; k < 16u; ++k)

			{
				m[k] = 0;
			}

			for (j = 0u; j < 16u; ++j)
			{
				m[j] = block_dummy[15 - j];
			}
			state[7] = m_state[7];
			state[6] = m_state[6];
			state[5] = m_state[5];
			state[4] = m_state[4];
			state[3] = m_state[3];
			state[2] = m_state[2];
			state[1] = m_state[1];
			state[0] = m_state[0];
			

			// states a b c
			// m_states h h h

			j = 0u;

			for (i = 0u; i < 64u; ++i)
			{
				insert_state("ctrl_rotationss");
				//j = i;
				if (i < 16)
				{

					w_data = m[i];
				}
				else
				{
					//w_temp = sig1(m[14]) + m[9] + sig0(m[1]) + m[0];
					w_temp = compute_w(m[14],m[9],m[1],m[0]);
					for (l = 0u; l < 15u; ++l)
					{
						m[l] = m[(l + 1)];
					}
					m[15] = w_temp;
					w_data = w_temp;
				}

				k_constant = K[i];

				maj = majority(state[0], state[1], state[2]);
				//xorA = rotr(state[0], 2u) ^ rotr(state[0], 13u) ^ rotr(state[0], 22u);
				xorA = mult_xor(state[0],2u,13u,22u);
				ch = choose(state[4], state[5], state[6]);

				//xorE = rotr(state[4], 6u) ^ rotr(state[4], 11u) ^ rotr(state[4], 25u);
				xorE = mult_xor(state[4],6u,11u,25u);
				sum = Summ(w_data, K[i], state[7u], ch, xorE); // m
				newA = newa(xorA, maj, sum);
				newE = newe(state[3], sum);

				state[7] = state[6];
				state[6] = state[5];
				state[5] = state[4];
				state[4] = newE;
				state[3] = state[2];
				state[2] = state[1];
				state[1] = state[0];
				state[0] = newA;
			}

			i = 0;

			insert_state("ctrl_done");
			m_state[7] = (state[7] + m_state[7]); // M_statea=H[0], States=A[b]
			m_state[6] = (state[6] + m_state[6]);
			m_state[5] = (state[5] + m_state[5]);
			m_state[4] = (state[4] + m_state[4]);
			m_state[3] = (state[3] + m_state[3]);
			m_state[2] = (state[2] + m_state[2]);
			m_state[1] = (state[1] + m_state[1]);
			m_state[0] = (state[0] + m_state[0]);

			digest_block->master_write(m_state);
		}
	}
};
#endif
