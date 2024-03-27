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


#ifndef SHA256_H
#define SHA256_H

#include "systemc.h"
#include "Interfaces.h"
#include <cstdint>

// Declare some constants to make the code easier to read
constexpr uint16_t DATA_WIDTH = 32;
constexpr uint16_t NUMBER_OF_MESSAGE_BLOCKS = 512 / DATA_WIDTH;
constexpr uint16_t NUMBER_OF_DIGEST_BLOCKS = 8;
const sc_uint<8> SHA256_ENDING = 0x80;

// Declare some type aliases to make the code easier to read
using MessageBlockType = std::array<uint32_t, NUMBER_OF_MESSAGE_BLOCKS>;
using DigestBlockType  = std::array<uint32_t, NUMBER_OF_DIGEST_BLOCKS>;

// Datatypes used for the communitcation with the environment
struct Sha256Request {
    bool     is_init;
    bool     is_next;
    bool     is_sha256_mode;
    bool     is_winternitz;
    bool     winternitz_n_mode;
    uint8_t  winternitz_w;
    uint8_t  winternitz_loop_init;
    bool     zerorize;
    MessageBlockType message_block;
};

struct Sha256Response {
    DigestBlockType digest_block;
};

// Datatypes used for the communication with the SHA256 core
// Using different datatypes/ports for the same hardware interface allows to write more abstract code
// and makes the code significantly easier to read, because a large amount of bitmanipulations can be
// moved from the code to the ESL to RTL mapping.
// ... for the regular SHA256 computation
struct Sha256CoreRequest {
    bool     init_command;
    bool     next_command;
    bool     is_sha256_mode;
    bool     zerorize;
    MessageBlockType message_block;
};
struct Sha256CoreResponse {
    DigestBlockType digest_block;
};


// ... for the winternitz computation in 256bit mode
using Tmp256Type  = std::array<uint32_t, 8>;
struct Winternitz256BlockType {
    sc_biguint<128> I;
    sc_uint< 32>    q;
    sc_uint< 16>    i;
    sc_uint<  8>    j;
    Tmp256Type tmp;
    sc_biguint< 72> padding;
};
struct Sha256CoreWinternitz256Request {
    bool                   init_command;
    bool                   next_command;
    bool                   is_sha256_mode;
    bool     zerorize;
    Winternitz256BlockType message_block;
};
struct Sha256CoreWinternitz256Response {
    Tmp256Type tmp;
};

// ... for the winternitz computation in 192bit mode
using Tmp192Type  = std::array<uint32_t, 6>;
struct Winternitz192BlockType {
    sc_biguint<128> I;
    sc_uint< 32>    q;
    sc_uint< 16>    i;
    sc_uint<  8>    j;
    Tmp192Type tmp;
    sc_biguint<136> padding;
};
struct Sha256CoreWinternitz192Request {
    bool                   init_command;
    bool                   next_command;
    bool                   is_sha256_mode;
    bool     zerorize;
    Winternitz192BlockType message_block;
};
struct Sha256CoreWinternitz192Response {
    Tmp192Type tmp;
};


SC_MODULE(sha256) {
    public:
        // Interface to the environment
        Sha256Request sha_request;
        blocking_in<Sha256Request> sha_request_port;
        shared_in<Sha256Request>   sha_shared_request_port;
        Sha256Response sha_response;
        master_out<Sha256Response> sha_response_port;

        // Interface to the sha256 core submodule for regular sha256 computation
        Sha256CoreRequest sha_core_request;
        master_out<Sha256CoreRequest>  sha_core_request_port;
        Sha256CoreResponse sha_core_response;
        blocking_in<Sha256CoreResponse> sha_core_response_port;

        // Interface to the sha256 core submodule for winternitz computations modes
        Sha256CoreWinternitz256Request sha_core_winternitz256_request;
        master_out<Sha256CoreWinternitz256Request>  sha_core_winternitz256_request_port;
        Sha256CoreWinternitz256Response sha_core_winternitz256_response;
        blocking_in<Sha256CoreWinternitz256Response> sha_core_winternitz256_response_port;

        Sha256CoreWinternitz192Request sha_core_winternitz192_request;
        master_out<Sha256CoreWinternitz192Request>  sha_core_winternitz192_request_port;
        Sha256CoreWinternitz192Response sha_core_winternitz192_response;
        blocking_in<Sha256CoreWinternitz192Response> sha_core_winternitz192_response_port;

        // Constructor
        SC_CTOR(sha256) {
            SC_THREAD(sha);
        }

    private:
        // The number of loop iterations to compute a key candidate are: 2^w - 1
        // Without the first iteration it is 2^w - 2
        uint8_t compute_winternitz_iterations(uint8_t winternitz_w) const {
            switch (winternitz_w) {
                case 0:
                    return 0;
                    break;

                case 2:
                    return 2;
                    break;

                case 4:
                    return 14;
                    break;

                case 8:
                    return 254;
                    break;

                default:
                    return 0;
                    break;
            }
        }

        bool invalid_winternitz_w(uint8_t winternitz_w) const {
            return (winternitz_w != 1 && 
                    winternitz_w != 2 &&
                    winternitz_w != 4 &&
                    winternitz_w != 8);
        }

        bool invalid_winternitz_j(uint8_t winternitz_loop_init, uint8_t loop_iterations) const {
            return (winternitz_loop_init > loop_iterations);
        }

        bool invalid_winternitz_mode(bool is_sha256_mode) const {
            return !is_sha256_mode;
        }

        bool is_winternitz_valid   = false;
        bool winternitz_error      = false;
        bool winternitz_error_w    = false;
        bool winternitz_error_j    = false;
        bool winternitz_error_mode = false;

        sc_biguint<128> winternitz_I = 0;
        sc_uint<32>     winternitz_q = 0;
        sc_uint<16>     winternitz_i = 0;

        uint8_t loop_counter  = 0;
        uint8_t loop_boundary;
        uint8_t loop_iterations;

        bool pending_sha_request = false;

        void sha() {
            pending_sha_request = false;
            while (true) {
                
                sha_request_port->read(sha_request, "idle");

                // Check if the request is for a valid winternitz computation
                loop_iterations =
                    compute_winternitz_iterations(sha_request.winternitz_w);

                is_winternitz_valid =
                    sha_request.is_init &&
                    sha_request.winternitz_loop_init <= loop_iterations;
                if (sha_request.is_winternitz && is_winternitz_valid) {

                    // winternitz_error_w = (
                    //     sha_request.winternitz_w != 1 && 
                    //     sha_request.winternitz_w != 2 &&
                    //     sha_request.winternitz_w != 4 &&
                    //     sha_request.winternitz_w != 8);

                    // winternitz_error_j =
                    //     (sha_request.winternitz_loop_init > loop_iterations);

                    // winternitz_error_mode = !sha_request.is_sha256_mode;

                    // winternitz_error =
                    //     winternitz_error_w ||
                    //     winternitz_error_j ||
                    //     winternitz_error_mode;
                        
                    // sha_error.winternitz_error = winternitz_error;
                    // sha_error_port->set(sha_error);

                    // Step1: Perform regular SHA256 computation
                    sha_core_request.init_command   = true;
                    sha_core_request.next_command   = false;
                    sha_core_request.is_sha256_mode = sha_request.is_sha256_mode;
                    sha_core_request.message_block  = sha_request.message_block;
                    sha_core_request.zerorize       = sha_request.zerorize;
                    sha_core_request_port->master_write(sha_core_request);

                        loop_counter  = sha_request.winternitz_loop_init;
                        loop_boundary = loop_iterations;

                        winternitz_I =
                            (sc_biguint<128>(sha_request.message_block[0]) << 96) +
                            (sc_biguint<128>(sha_request.message_block[1]) << 64) +
                            (sc_biguint<128>(sha_request.message_block[2]) << 32) +
                            (sc_biguint<128>(sha_request.message_block[3])      );
                        winternitz_q =
                            sc_uint<32>(sha_request.message_block[4]);
                        winternitz_i =
                            sc_uint<16>(sha_request.message_block[5] >> 16);

                        if(sha_request.winternitz_n_mode) {

                            sha_core_winternitz256_response_port->read(sha_core_winternitz256_response, "lms_1st_256");
                            sha_response.digest_block = sha_core_winternitz256_response.tmp;
                            while (loop_counter < loop_boundary) {
                                loop_counter += 1;

                                // Next stop: Perform 256 bit winternitz computation
                                sha_core_winternitz256_request.init_command   = true;
                                sha_core_winternitz256_request.next_command   = false;
                                sha_core_winternitz256_request.is_sha256_mode = true;
                                sha_core_winternitz256_request.message_block.I       = winternitz_I;
                                sha_core_winternitz256_request.message_block.q       = winternitz_q;
                                sha_core_winternitz256_request.message_block.i       = winternitz_i;
                                sha_core_winternitz256_request.message_block.j       =
                                    static_cast<sc_uint<8>>(loop_counter);
                                sha_core_winternitz256_request.message_block.tmp     =
                                    sha_core_winternitz256_response.tmp;
                                sha_core_winternitz256_request.message_block.padding =
                                    (sc_biguint<72>(SHA256_ENDING) << 64) +
                                    //(sc_biguint<72>(0x80) << 64) +
                                    (sc_biguint<72>(0x01b8));
                                sha_core_winternitz256_request.zerorize = sha_request.zerorize;
                                sha_core_winternitz256_request_port->master_write(sha_core_winternitz256_request);

                                sha_core_winternitz256_response_port->read(sha_core_winternitz256_response, "lms_others_256");
                                sha_response.digest_block = sha_core_winternitz256_response.tmp;
                            }

                        } else {

                            sha_core_winternitz192_response_port->read(sha_core_winternitz192_response, "lms_1st_192");
                            sha_response.digest_block[0] = sha_core_winternitz192_response.tmp[0];
                            sha_response.digest_block[1] = sha_core_winternitz192_response.tmp[1];
                            sha_response.digest_block[2] = sha_core_winternitz192_response.tmp[2];
                            sha_response.digest_block[3] = sha_core_winternitz192_response.tmp[3];
                            sha_response.digest_block[4] = sha_core_winternitz192_response.tmp[4];
                            sha_response.digest_block[5] = sha_core_winternitz192_response.tmp[5];
                            sha_response.digest_block[6] = 0;
                            sha_response.digest_block[7] = 0;
                            while (loop_counter < loop_boundary) {
                                loop_counter += 1;

                                // Next stop: Perform 192 bit winternitz computation
                                sha_core_winternitz192_request.init_command   = true;
                                sha_core_winternitz192_request.next_command   = false;
                                sha_core_winternitz192_request.is_sha256_mode = true;
                                sha_core_winternitz192_request.message_block.I       = winternitz_I;
                                sha_core_winternitz192_request.message_block.q       = winternitz_q;
                                sha_core_winternitz192_request.message_block.i       = winternitz_i;
                                sha_core_winternitz192_request.message_block.j       =
                                    static_cast<sc_uint<8>>(loop_counter);
                                sha_core_winternitz192_request.message_block.tmp     =
                                    sha_core_winternitz192_response.tmp;
                                sha_core_winternitz192_request.message_block.padding =
                                    (sc_biguint<136>(SHA256_ENDING) << 128) +
                                    //(sc_biguint<136>(0x80) << 128) +
                                    (sc_biguint<136>(0x0178));
                                sha_core_winternitz192_request.zerorize = sha_request.zerorize;
                                sha_core_winternitz192_request_port->master_write(sha_core_winternitz192_request);

                                sha_core_winternitz192_response_port->read(sha_core_winternitz192_response, "lms_others_192");
                                sha_response.digest_block[0] = sha_core_winternitz192_response.tmp[0];
                                sha_response.digest_block[1] = sha_core_winternitz192_response.tmp[1];
                                sha_response.digest_block[2] = sha_core_winternitz192_response.tmp[2];
                                sha_response.digest_block[3] = sha_core_winternitz192_response.tmp[3];
                                sha_response.digest_block[4] = sha_core_winternitz192_response.tmp[4];
                                sha_response.digest_block[5] = sha_core_winternitz192_response.tmp[5];
                                sha_response.digest_block[6] = 0;
                                sha_response.digest_block[7] = 0;
                            }
                        }

                    // Send out the computed result
                    sha_response_port->master_write(sha_response);

                } else {

                    // sha_error.winternitz_error = false;

                    while(sha_request.is_init || sha_request.is_next) {
                    //do {
                        // Perform regular SHA operation
                        sha_core_request.init_command   = sha_request.is_init;
                        sha_core_request.next_command   = sha_request.is_next;
                        sha_core_request.is_sha256_mode = sha_request.is_sha256_mode;
                        sha_core_request.message_block  = sha_request.message_block;
                        sha_core_request.zerorize       = sha_request.zerorize;
                        sha_core_request_port->master_write(sha_core_request);

                        sha_core_response_port->read(sha_core_response, "sha");

                        sha_response.digest_block = sha_core_response.digest_block;
                        sha_response.digest_block[7] = sha_request.is_sha256_mode ? sha_response.digest_block[7] : 0;
                        //if (!sha_request.is_sha256_mode) {
                        //    sha_response.digest_block[7] = 0;
                        //}

                        // Send out the computed result
                        sha_response_port->master_write(sha_response);

                        // Check if the next request is already there
                        sha_shared_request_port->get(sha_request);
                    }
                    //} while(true);
                }
            }
        }
};

#endif