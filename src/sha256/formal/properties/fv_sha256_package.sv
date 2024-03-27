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
package sha256_package;

typedef enum logic [2:0] {WNTZ_IDLE, WNTZ_1ST, WNTZ_OTHERS} wntz_fsm_t;

typedef logic unsigned [31:0] a_unsigned_32_16 [15:0];

typedef struct {
  logic init_command;
  logic next_command;
  logic is_sha256_mode;
  logic zeroize;
  a_unsigned_32_16 message_block;
} st_Sha256CoreRequest;

typedef logic unsigned [31:0] a_unsigned_32_8 [7:0];

typedef struct {
  a_unsigned_32_8 digest_block;
} st_Sha256CoreResponse;

typedef logic unsigned [31:0] a_unsigned_32_6 [5:0];

typedef struct {
  logic unsigned [127:0] I;
  logic unsigned [31:0] q;
  logic unsigned [15:0] i;
  logic unsigned [7:0] j;
  a_unsigned_32_6 tmp;
  logic unsigned [135:0] padding;
} st_Winternitz192BlockType;

typedef struct {
  logic init_command;
  logic next_command;
  logic is_sha256_mode;
  logic zeroize;
  st_Winternitz192BlockType message_block;
} st_Sha256CoreWinternitz192Request;

typedef struct {
  a_unsigned_32_6 tmp;
} st_Sha256CoreWinternitz192Response;

typedef struct {
  logic unsigned [127:0] I;
  logic unsigned [31:0] q;
  logic unsigned [15:0] i;
  logic unsigned [7:0] j;
  a_unsigned_32_8 tmp;
  logic unsigned [71:0] padding;
} st_Winternitz256BlockType;

typedef struct {
  logic init_command;
  logic next_command;
  logic is_sha256_mode;
  logic zeroize;
  st_Winternitz256BlockType message_block;
} st_Sha256CoreWinternitz256Request;

typedef struct {
  a_unsigned_32_8 tmp;
} st_Sha256CoreWinternitz256Response;

typedef struct {
  logic is_init;
  logic is_next;
  logic is_sha256_mode;
  logic is_winternitz;
  logic winternitz_n_mode;
  logic unsigned [7:0] winternitz_w;
  logic unsigned [7:0] winternitz_loop_init;
  logic zeroize;
  a_unsigned_32_16 message_block;
} st_Sha256Request;

typedef struct {
  a_unsigned_32_8 digest_block;
} st_Sha256Response;


// Constants

parameter logic unsigned [7:0] SHA256_ENDING = 8'h80;


endpackage
