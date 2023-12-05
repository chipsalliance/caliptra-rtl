
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

#ifndef SHA256_MEMORY_H
#define SHA256_MEMORY_H

#include "systemc.h"
#include "Interfaces.h"
#include <iomanip>
#include <string>
#include <array>
#include <iostream>
#include <chrono>
#include <cstring>
#include <sstream>

SC_MODULE(sha256_memory)
{

public:
	blocking_in<std::string> block;
	blocking_out<std::array<uint32_t, 16>> w;
	blocking_out< int> next;
	blocking_out< int> ctrl_done;
	blocking_out< int> init_transfrom;

	SC_CTOR(sha256_memory)
	{
		SC_THREAD(mem);
	}

private:
	uint32_t m_blocklen = 0, m[16] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
	uint64_t m_bitlen = 0;
	uint8_t m_data[64] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
	std::array<uint32_t, 16> mj = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
	std::string block_dummy;

	void update(const uint8_t *data, size_t length)
	{
		m_bitlen = 0;
		m_blocklen = 0;

		for (size_t i = 0; i < length; i++)
		{
			m_data[m_blocklen++] = data[i];

			if (m_blocklen == 64)
			{

				for (uint8_t i = 0, j = 0; i < 16; i++, j += 4)
				{
					m[i] = (m_data[j] << 24) | (m_data[j + 1] << 16) | (m_data[j + 2] << 8) | (m_data[j + 3]);
				}
				for (int i = 0; i < 16; i++)
				{

					mj[i] = m[i];
				}

				if (m_bitlen < 512)
				{

					ctrl_done->write(0);
					next->write(0);
					init_transfrom->write(1);
					w->write(mj);
				}

				else
				{
					ctrl_done->write(0);
					next->write(1);
					init_transfrom->write(0);
					w->write(mj);
				}

				m_bitlen = m_bitlen + 512;
				m_blocklen = 0;
			}
		}
	}

	void update(const std::string &data)
	{
		update(reinterpret_cast<const uint8_t *>(data.c_str()), data.size());
	}

	void mem()

	{

		while (true)
		{

			block->read(block_dummy);

			update(block_dummy);

			uint64_t i = m_blocklen;
			uint8_t end = m_blocklen < 56 ? 56 : 64;
			m_data[i++] = 0x80; // Append a bit 1
			while (i < end)

			{
				m_data[i++] = 0x00; // Pad with zeros
			}

			if (m_blocklen >= 56)
			{
				for (uint8_t i = 0, j = 0; i < 16; i++, j += 4)

				{
					m[i] = (m_data[j] << 24) | (m_data[j + 1] << 16) | (m_data[j + 2] << 8) | (m_data[j + 3]);
				}

				for (int i = 0; i < 16; i++)
				{

					mj[i] = m[i];
				}

				if (m_bitlen < 512)
				{
					ctrl_done->write(0);
					next->write(0);
					init_transfrom->write(1);
					w->write(mj);
				}

				else
				{
					ctrl_done->write(0);
					next->write(1);
					init_transfrom->write(0);
					w->write(mj);
				}
				memset(m_data, 0, 56);
			}

			// Append to the padding the total message's length in bits and transform.
			m_bitlen += m_blocklen * 8;
			m_data[63] = m_bitlen;
			m_data[62] = m_bitlen >> 8;
			m_data[61] = m_bitlen >> 16;
			m_data[60] = m_bitlen >> 24;
			m_data[59] = m_bitlen >> 32;
			m_data[58] = m_bitlen >> 40;
			m_data[57] = m_bitlen >> 48;
			m_data[56] = m_bitlen >> 56;
			for (uint8_t i = 0, j = 0; i < 16; i++, j += 4)

			{
				m[i] = (m_data[j] << 24) | (m_data[j + 1] << 16) | (m_data[j + 2] << 8) | (m_data[j + 3]);
			}
			for (uint32_t i = 0; i < 16; i++)
			{

				mj[i] = m[i];
			}
			ctrl_done->write(1);
			next->write(0);
			init_transfrom->write(0);
			w->write(mj);
		}
	}
};
#endif