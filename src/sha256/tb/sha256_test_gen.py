#/usr/local/bin/python3
# SPDX-License-Identifier: Apache-2.0
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
#
import os
import subprocess
import random

def generate_expected_digest():
    f = open("sha256_test_vector.txt", "r")
    g = open("expected_digest.txt", "w")
    h = open("expected_digests_all.txt", "a")
    block_str = ""
    digest_str = ""

    for line in f:
        if(line[0:8] == "BLOCK = "):
            block_str = line.strip()[8:]    

    #Generate digest using OpenSSL HMAC SHA384
    command = 'echo '+block_str+' | xxd -r -p | openssl dgst -sha256'
    digest = subprocess.check_output(command, shell=True)
    digest_str = str(digest)

    #Chomp extra chars at beginning and end if python 3.6.8 is loaded
    if digest_str[1] == "'":
        digest_str = digest_str[11:-3]
    else:
        digest_str = digest_str.rstrip()
        digest_str = digest_str[9:]
    g.write('DIGEST = '+digest_str+'\n')
    h.write('DIGEST = '+digest_str+'\n')
    h.write("------------------------\n")


    f.close()
    g.close()
    h.close()

def main():
    generate_expected_digest()

main()
