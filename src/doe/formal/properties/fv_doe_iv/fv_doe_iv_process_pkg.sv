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


package doe_iv_process_pkg;


  typedef struct {
    bit unsigned [127:0] encoded_msg;
    bit unsigned [127:0] block_msg;
    bit unsigned [127:0] IV;
    bit encdec;
    bit enc_ready;
    bit dec_ready;
    bit IV_Updated_d;
    bit next_cmd;
    bit keylen;
  } st_InPacket;


endpackage
