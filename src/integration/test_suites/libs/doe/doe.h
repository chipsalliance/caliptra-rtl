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

#ifndef DOE_H
  #define DOE_H

#include "stdint.h"

#define DOE_HEK_DES 22

/* --------------- symbols/typedefs --------------- */
enum doe_cmd_e {
    DOE_IDLE = 0,
    DOE_UDS = 1,
    DOE_FE = 2,
    DOE_CLEAR_OBF_SECRETS = 3,
    DOE_HEK = 4
};

/* --------------- Function Prototypes --------------- */
void doe_init(uint32_t * iv_data_uds, uint32_t * iv_data_fe, uint32_t * iv_data_hek, uint32_t kv_dest_fe);
void doe_clear_secrets();

#endif
