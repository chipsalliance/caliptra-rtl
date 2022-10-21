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
#ifndef HMAC_REG_HEADER
#define HMAC_REG_HEADER


#define HMAC_REG_HMAC384_NAME_0                                                 (0x0)
#define HMAC_REG_HMAC384_NAME_1                                                 (0x4)
#define HMAC_REG_HMAC384_VERSION_0                                              (0x8)
#define HMAC_REG_HMAC384_VERSION_1                                              (0xc)
#define HMAC_REG_HMAC384_CTRL                                                   (0x10)
#define HMAC_REG_HMAC384_CTRL_INIT_LOW                                          (0)
#define HMAC_REG_HMAC384_CTRL_INIT_MASK                                         (0x1)
#define HMAC_REG_HMAC384_CTRL_NEXT_LOW                                          (1)
#define HMAC_REG_HMAC384_CTRL_NEXT_MASK                                         (0x2)
#define HMAC_REG_HMAC384_STATUS                                                 (0x18)
#define HMAC_REG_HMAC384_STATUS_READY_LOW                                       (0)
#define HMAC_REG_HMAC384_STATUS_READY_MASK                                      (0x1)
#define HMAC_REG_HMAC384_STATUS_VALID_LOW                                       (1)
#define HMAC_REG_HMAC384_STATUS_VALID_MASK                                      (0x2)
#define HMAC_REG_HMAC384_KEY_0                                                  (0x40)
#define HMAC_REG_HMAC384_KEY_1                                                  (0x44)
#define HMAC_REG_HMAC384_KEY_2                                                  (0x48)
#define HMAC_REG_HMAC384_KEY_3                                                  (0x4c)
#define HMAC_REG_HMAC384_KEY_4                                                  (0x50)
#define HMAC_REG_HMAC384_KEY_5                                                  (0x54)
#define HMAC_REG_HMAC384_KEY_6                                                  (0x58)
#define HMAC_REG_HMAC384_KEY_7                                                  (0x5c)
#define HMAC_REG_HMAC384_KEY_8                                                  (0x60)
#define HMAC_REG_HMAC384_KEY_9                                                  (0x64)
#define HMAC_REG_HMAC384_KEY_10                                                 (0x68)
#define HMAC_REG_HMAC384_KEY_11                                                 (0x6c)
#define HMAC_REG_HMAC384_BLOCK_0                                                (0x80)
#define HMAC_REG_HMAC384_BLOCK_1                                                (0x84)
#define HMAC_REG_HMAC384_BLOCK_2                                                (0x88)
#define HMAC_REG_HMAC384_BLOCK_3                                                (0x8c)
#define HMAC_REG_HMAC384_BLOCK_4                                                (0x90)
#define HMAC_REG_HMAC384_BLOCK_5                                                (0x94)
#define HMAC_REG_HMAC384_BLOCK_6                                                (0x98)
#define HMAC_REG_HMAC384_BLOCK_7                                                (0x9c)
#define HMAC_REG_HMAC384_BLOCK_8                                                (0xa0)
#define HMAC_REG_HMAC384_BLOCK_9                                                (0xa4)
#define HMAC_REG_HMAC384_BLOCK_10                                               (0xa8)
#define HMAC_REG_HMAC384_BLOCK_11                                               (0xac)
#define HMAC_REG_HMAC384_BLOCK_12                                               (0xb0)
#define HMAC_REG_HMAC384_BLOCK_13                                               (0xb4)
#define HMAC_REG_HMAC384_BLOCK_14                                               (0xb8)
#define HMAC_REG_HMAC384_BLOCK_15                                               (0xbc)
#define HMAC_REG_HMAC384_BLOCK_16                                               (0xc0)
#define HMAC_REG_HMAC384_BLOCK_17                                               (0xc4)
#define HMAC_REG_HMAC384_BLOCK_18                                               (0xc8)
#define HMAC_REG_HMAC384_BLOCK_19                                               (0xcc)
#define HMAC_REG_HMAC384_BLOCK_20                                               (0xd0)
#define HMAC_REG_HMAC384_BLOCK_21                                               (0xd4)
#define HMAC_REG_HMAC384_BLOCK_22                                               (0xd8)
#define HMAC_REG_HMAC384_BLOCK_23                                               (0xdc)
#define HMAC_REG_HMAC384_BLOCK_24                                               (0xe0)
#define HMAC_REG_HMAC384_BLOCK_25                                               (0xe4)
#define HMAC_REG_HMAC384_BLOCK_26                                               (0xe8)
#define HMAC_REG_HMAC384_BLOCK_27                                               (0xec)
#define HMAC_REG_HMAC384_BLOCK_28                                               (0xf0)
#define HMAC_REG_HMAC384_BLOCK_29                                               (0xf4)
#define HMAC_REG_HMAC384_BLOCK_30                                               (0xf8)
#define HMAC_REG_HMAC384_BLOCK_31                                               (0xfc)
#define HMAC_REG_HMAC384_TAG_0                                                  (0x100)
#define HMAC_REG_HMAC384_TAG_1                                                  (0x104)
#define HMAC_REG_HMAC384_TAG_2                                                  (0x108)
#define HMAC_REG_HMAC384_TAG_3                                                  (0x10c)
#define HMAC_REG_HMAC384_TAG_4                                                  (0x110)
#define HMAC_REG_HMAC384_TAG_5                                                  (0x114)
#define HMAC_REG_HMAC384_TAG_6                                                  (0x118)
#define HMAC_REG_HMAC384_TAG_7                                                  (0x11c)
#define HMAC_REG_HMAC384_TAG_8                                                  (0x120)
#define HMAC_REG_HMAC384_TAG_9                                                  (0x124)
#define HMAC_REG_HMAC384_TAG_10                                                 (0x128)
#define HMAC_REG_HMAC384_TAG_11                                                 (0x12c)


#endif