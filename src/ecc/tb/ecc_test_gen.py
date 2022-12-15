#usr/local/bin/python3
#********************************************************************************
# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#********************************************************************************
import os
import subprocess
import re

def generate_test():
    # Open file for logging outputs
    f = open("keygen_vectors_no_hmac_drbg.hex", "w")
    g = open("ref_keygen_vectors_no_hmac_drbg.hex", "a")

    # Generate random private and public key pair
    subprocess.run('openssl ecparam -name secp384r1 -genkey -noout -out key.pem', shell = True)
    subprocess.run('openssl ec -in key.pem -text -out key.txt', shell = True)

    private_key_flag = 0
    public_key_flag = 0
    public_key_x_flag = 0
    public_key_y_flag = 0

    byte_count = 0
    bytes_per_line = 15
    bytes_per_key = 48

    private_key = ''
    public_key_x = ''
    public_key_y = ''

    # Parse key_txt and write test vectors to file
    with open('key.txt') as k:
        for line in k:
            if (re.match("^priv:$", line)):
                private_key_flag = 1
            elif ((private_key_flag == 1) and (byte_count == 0) and (re.match("^\s+00:[0-9a-f]{2}:.*", line))):
                private_key += line.strip()[3:].replace(':', '')
                byte_count += 14
            elif (private_key_flag == 1 and re.match("^\s+[0-9a-f]{2}:.*", line)):
                private_key += line.strip().replace(':', '')
                if (byte_count == 44):
                    byte_count += 4
                elif (byte_count == 43):
                    byte_count += 3
                else:
                    byte_count += bytes_per_line
            elif (re.match("^pub:", line)):
                private_key_flag = 0
                public_key_flag = 1
                public_key_x_flag = 1
                byte_count = 0
            elif (public_key_flag == 1 and re.match("^\s+[0-9a-f]{2}:.*", line)):
                if (public_key_x_flag == 1 and byte_count == 0): 
                    public_key_x += line.strip()[3:].replace(':', '')
                    # First byte of public key is 04 to indicate uncompressed key, so we will ingore this byte
                    byte_count += 14
                elif (public_key_x_flag == 1 and (byte_count == 14 or byte_count == 29)):
                    public_key_x += line.strip().replace(':', '')
                    byte_count += bytes_per_line
                elif (public_key_x_flag == 1 and byte_count == 44):
                    public_key_x += line.strip()[0:12].replace(':', '')
                    byte_count += 4
                    if (byte_count == bytes_per_key):
                        byte_count = 0
                        public_key_x_flag = 0
                        public_key_y_flag = 1
                    public_key_y += line.strip()[12:].replace(':', '')
                    byte_count += 11
                elif (public_key_y_flag == 1):
                    public_key_y += line.strip().replace(':', '')
                    byte_count += bytes_per_line
                    if (byte_count == bytes_per_key):
                        byte_count = 0
                        public_key_y_flag = 0
                        public_key_flag = 0

    print(private_key)
    print('\n')
    print(public_key_x)
    print('\n')
    print(public_key_y)
    print('\n')

    f.write(private_key + '\n')
    f.write(public_key_x + '\n')
    f.write(public_key_y + '\n')

    g.write(private_key + '\n')
    g.write(public_key_x + '\n')
    g.write(public_key_y + '\n')
    g.write('\n')

    f.close()
    g.close()
    k.close()

generate_test()