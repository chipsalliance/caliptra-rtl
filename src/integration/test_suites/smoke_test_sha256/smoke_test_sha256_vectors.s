/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
.data
hw_data:
// start of input message
// SHA224 test
.word 0x61626380
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000018
// expected value
.word 0x23097D22
.word 0x3405D822
.word 0x8642A477
.word 0xBDA255B3
.word 0x2AADBCE4
.word 0xBDA0B3F7
.word 0xE36C9DA7
.word 0x00000000
// .ascii "----------------------------------\n"
// .ascii "SHA256 test !!\n"
// .ascii "----------------------------------\n"
// .byte 0
SHA256ShortMsg:
// SHA256ShortMsgvector_2
// vector length
.word 0x00000008
// input message
.word 0x61626380
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000018
// expected output
.word 0xBA7816BF
.word 0x8F01CFEA
.word 0x414140DE
.word 0x5DAE2223
.word 0xB00361A3
.word 0x96177A9C
.word 0xB410FF61
.word 0xF20015AD
