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
#ifndef MBOX_CSR_HEADER
#define MBOX_CSR_HEADER


#define MBOX_CSR_MBOX_LOCK                                                      (0x0)
#define MBOX_CSR_MBOX_LOCK_LOCK_LOW                                             (0)
#define MBOX_CSR_MBOX_LOCK_LOCK_MASK                                            (0x1)
#define MBOX_CSR_MBOX_USER                                                      (0x4)
#define MBOX_CSR_MBOX_CMD                                                       (0x8)
#define MBOX_CSR_MBOX_DLEN                                                      (0xc)
#define MBOX_CSR_MBOX_DATAIN                                                    (0x10)
#define MBOX_CSR_MBOX_DATAOUT                                                   (0x14)
#define MBOX_CSR_MBOX_EXECUTE                                                   (0x18)
#define MBOX_CSR_MBOX_EXECUTE_EXECUTE_LOW                                       (0)
#define MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK                                      (0x1)
#define MBOX_CSR_MBOX_STATUS                                                    (0x1c)
#define MBOX_CSR_MBOX_STATUS_STATUS_LOW                                         (0)
#define MBOX_CSR_MBOX_STATUS_STATUS_MASK                                        (0x3)


#endif