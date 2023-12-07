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
#include <iomanip>
#include <iostream>
#include <chrono>
#include <string>
#include <array>
#include <cstring>
#include <sstream>

SC_MODULE(sha256_core)
{
public:
	uint32_t maj, xorA, ch, xorE, sum, newA, newE;
	std::array<uint32_t, 64> m;
	std::array<uint32_t, 8> state;
	std::array<uint32_t, 64> K;
	std::array<uint32_t, 8> m_state;
	std::array<uint32_t, 16> n;
	std::array<uint32_t, 32> hashing;//uint8
	uint32_t i, k;
	uint32_t j;
	int next_dummy, init_transform_dummy, ctrl_done_dummy, mode_dummy;

	blocking_in<std::array<uint32_t, 16>> w_core;
	blocking_in<int> mode;
#define loopstart 0u
#define loopbound 2u
#define incr 1u

#ifdef SIMULATION

	blocking_out<std::string> digest_block;
#else
	blocking_out<std::array<uint32_t, 32>> digest_block;//uint8
#endif

	blocking_in<int> next_signal, init_signal, ctrl_done;

	SC_CTOR(sha256_core)
	{
		SC_THREAD(fsm);
	}

	uint32_t rotr(uint32_t x, uint32_t n) const
	{
		return (x >> n) | (x << (32u - n));
	}
	uint32_t choose(uint32_t e, uint32_t f, uint32_t g) const
	{
		return (e & f) ^ (~e & g);
	}
	uint32_t majority(uint32_t a, uint32_t b, uint32_t c) const
	{
		return (a & (b | c)) | (b & c);
	}
	uint32_t sig0(uint32_t x) const
	{
		return rotr(x, 7u) ^ rotr(x, 18u) ^ (x >> 3u);
	}
	uint32_t sig1(uint32_t x) const
	{
		return rotr(x, 17u) ^ rotr(x, 19u) ^ (x >> 10u);
	}

	void fsm()
	{
		K[0] = 0x428a2f98u;
		K[1] = 0x71374491u;
		K[2] = 0xb5c0fbcfu;
		K[3] = 0xe9b5dba5u;
		K[4] = 0x3956c25bu;
		K[5] = 0x59f111f1u;
		K[6] = 0x923f82a4u;
		K[7] = 0xab1c5ed5u;
		K[8] = 0xd807aa98u;
		K[9] = 0x12835b01u;
		K[10] = 0x243185beu;
		K[11] = 0x550c7dc3u;
		K[12] = 0x72be5d74u;
		K[13] = 0x80deb1feu;
		K[14] = 0x9bdc06a7u;
		K[15] = 0xc19bf174u;
		K[16] = 0xe49b69c1u;
		K[17] = 0xefbe4786u;
		K[18] = 0x0fc19dc6u;
		K[19] = 0x240ca1ccu;
		K[20] = 0x2de92c6fu;
		K[21] = 0x4a7484aau;
		K[22] = 0x5cb0a9dcu;
		K[23] = 0x76f988dau;
		K[24] = 0x983e5152u;
		K[25] = 0xa831c66du;
		K[26] = 0xb00327c8u;
		K[27] = 0xbf597fc7u;
		K[28] = 0xc6e00bf3u;
		K[29] = 0xd5a79147u;
		K[30] = 0x06ca6351u;
		K[31] = 0x14292967u;
		K[32] = 0x27b70a85u;
		K[33] = 0x2e1b2138u;
		K[34] = 0x4d2c6dfcu;
		K[35] = 0x53380d13u;
		K[36] = 0x650a7354u;
		K[37] = 0x766a0abbu;
		K[38] = 0x81c2c92eu;
		K[39] = 0x92722c85u;
		K[40] = 0xa2bfe8a1u;
		K[41] = 0xa81a664bu;
		K[42] = 0xc24b8b70u;
		K[43] = 0xc76c51a3u;
		K[44] = 0xd192e819u;
		K[45] = 0xd6990624u;
		K[46] = 0xf40e3585u;
		K[47] = 0x106aa070u;
		K[48] = 0x19a4c116u;
		K[49] = 0x1e376c08u;
		K[50] = 0x2748774cu;
		K[51] = 0x34b0bcb5u;
		K[52] = 0x391c0cb3u;
		K[53] = 0x4ed8aa4au;
		K[54] = 0x5b9cca4fu;
		K[55] = 0x682e6ff3u;
		K[56] = 0x748f82eeu;
		K[57] = 0x78a5636fu;
		K[58] = 0x84c87814u;
		K[59] = 0x8cc70208u;
		K[60] = 0x90befffau;
		K[61] = 0xa4506cebu;
		K[62] = 0xbef9a3f7u;
		K[63] = 0xc67178f2u;
		m_state[0] = 0x0u;
		m_state[1] = 0x0u;
		m_state[2] = 0x0u;
		m_state[3] = 0x0u;
		m_state[4] = 0x0u;
		m_state[5] = 0x0u;
		m_state[6] = 0x0u;
		m_state[7] = 0x0u;
		state[0] = 0x0u;
		state[1] = 0x0u;
		state[2] = 0x0u;
		state[3] = 0x0u;
		state[4] = 0x0u;
		state[5] = 0x0u;
		state[6] = 0x0u;
		state[7] = 0x0u;
		while (true)

		{
			mode->read(mode_dummy, "idle");
			ctrl_done->read(ctrl_done_dummy, "idle");
			next_signal->read(next_dummy, "idle");
			init_signal->read(init_transform_dummy, "idle");

			if (mode_dummy == 0)
			{
				m_state[0] = 0x6a09e667u;
				m_state[1] = 0xbb67ae85u;
				m_state[2] = 0x3c6ef372u;
				m_state[3] = 0xa54ff53au;
				m_state[4] = 0x510e527fu;
				m_state[5] = 0x9b05688cu;
				m_state[6] = 0x1f83d9abu;
				m_state[7] = 0x5be0cd19u;
			}
			else if (mode_dummy == 1)
			{

				m_state[0] = 0xc1059ed8u;
				m_state[1] = 0x367cd507u;
				m_state[2] = 0x3070dd17u;
				m_state[3] = 0xf70e5939u;
				m_state[4] = 0xffc00b31u;
				m_state[5] = 0x68581511u;
				m_state[6] = 0x64f98fa7u;
				m_state[7] = 0xbefa4fa4u;
			}

			if (next_dummy == 1 || init_transform_dummy == 1 || ctrl_done_dummy == 1)
			{

				if (next_dummy == 1 || init_transform_dummy == 1 || ctrl_done_dummy == 1)

				{

					w_core->read(n, "ctrl_rotation");
					for (j = 0u; j < 8u; ++j) // 16
					{

						m[j] = n[j];
					}

					for (k = 0u; k < 2u; ++k) // 64
					{
						m[k] = sig1(m[k - 2u]) + m[k - 7u] + sig0(m[k - 15u]) + m[k - 16u];
					}

					for (i = 0u; i < 8u; ++i)
					{
						state[i] = m_state[i];
					}

				for (i = 0u; i < 2u; ++i) // 64
					{
						maj = majority(state[0], state[1], state[2]);
						xorA = rotr(state[0], 2u) ^ rotr(state[0], 13u) ^ rotr(state[0], 22u);

						ch = choose(state[4], state[5], state[6]);

						xorE = rotr(state[4], 6u) ^ rotr(state[4], 11u) ^ rotr(state[4], 25u);

						sum = m[i] + K[i] + state[7u] + ch + xorE;
						newA = xorA + maj + sum;
						newE = state[3] + sum;

						state[7] = state[6];
						state[6] = state[5];
						state[5] = state[4];
						state[4] = newE;
						state[3] = state[2];
						state[2] = state[1];
						state[1] = state[0];
						state[0] = newA;
					}

					/*for (i = 0u; i < 8u; ++i) // 8
					{										//The error is here. 
					m_state[i]+=state[i];
					}*/
				}
			}
			if (next_dummy == 0 && init_transform_dummy == 0 && ctrl_done_dummy == 1)
			{

				for (i = 0u; i < 1u; ++i) // 4
				{
					for (k = 0u; k < 2u; ++k) // 8
					{
						hashing[i + (k * 4u)] = (m_state[k] >> (24u - i * 8u))& 0x000000ffu; 
					}
				}
			}
#ifdef SIMULATION
			std::stringstream s;				// THIS PART IS FOR TESTING
			s << std::setfill('0') << std::hex; // THIS PART IS FOR TESTING
			if (mode_dummy == 0)
			{
				for (uint8_t i = 0; i < 32; i++) // THIS PART IS FOR TESTING
				{
					s << std::setw(2) << (unsigned int)hashing[i]; // THIS PART IS FOR TESTING
				}
			}
			else
			{
				for (uint8_t i = 0; i < 28; i++) // THIS PART IS FOR TESTING
				{
					s << std::setw(2) << (unsigned int)hashing[i]; // THIS PART IS FOR TESTING
				}

			}										   // THIS PART IS FOR TESTING
			digest_block->write(s.str(), "ctrl_done"); // THIS PART IS FOR TESTING
#else
			digest_block->write(hashing, "ctrl_done");
#endif

			if (mode_dummy == 0)
			{
				m_state[0] = 0x6a09e667u;
				m_state[1] = 0xbb67ae85u;
				m_state[2] = 0x3c6ef372u;
				m_state[3] = 0xa54ff53au;
				m_state[4] = 0x510e527fu;
				m_state[5] = 0x9b05688cu;
				m_state[6] = 0x1f83d9abu;
				m_state[7] = 0x5be0cd19u;
			}
			else if (mode_dummy == 1)
			{

				m_state[0] = 0xc1059ed8u;
				m_state[1] = 0x367cd507u;
				m_state[2] = 0x3070dd17u;
				m_state[3] = 0xf70e5939u;
				m_state[4] = 0xffc00b31u;
				m_state[5] = 0x68581511u;
				m_state[6] = 0x64f98fa7u;
				m_state[7] = 0xbefa4fa4u;
			}
		} 
	}
};
#endif
