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

def _generate_expected_tag(infile, outfile, all_file, hash_name):
    """Compute HMAC tag for a single test vector and emit a TAG line."""
    f = open(infile, "r")
    g = open(outfile, "w")
    h = open(all_file, "a")
    msg_str = ""
    key_str = ""
    seed_str = ""
    tag_str = ""

    for line in f:
        if line[0:6] == "KEY = ":
            key_str = line.strip()[6:]
        elif line[0:7] == "SEED = ":
            seed_str = line.strip()[7:]
        else:
            msg_str = msg_str + line.strip()[8:]

    # Generate digest using OpenSSL HMAC with the requested SHA variant.
    command = ('echo ' + msg_str + ' | xxd -r -p | openssl dgst -' + hash_name +
               ' -mac hmac -macopt hexkey:' + key_str + ' -hex')
    tag = subprocess.check_output(command, shell=True)
    tag_str = str(tag)

    # Chomp extra chars at beginning and end if python 3.6.8 is loaded.
    if tag_str[1] == "'":
        tag_str = tag_str[11:-3]
    else:
        tag_str = tag_str.rstrip()
        tag_str = tag_str[9:]
    g.write('TAG = ' + tag_str + '\n')
    h.write('TAG = ' + tag_str + '\n')
    h.write("------------------------\n")

    f.close()
    g.close()
    h.close()


def generate_expected_hmac224_tag():
    _generate_expected_tag("hmac256_uvm_test_vector_224.txt",
                           "expected_hmac224_tag.txt",
                           "expected_hmac224_tags_all.txt",
                           "sha224")


def generate_expected_hmac256_tag():
    _generate_expected_tag("hmac256_uvm_test_vector.txt",
                           "expected_hmac256_tag.txt",
                           "expected_hmac256_tags_all.txt",
                           "sha256")


def main():
    hmac224_file = 'hmac256_uvm_test_vector_224.txt'
    hmac256_file = 'hmac256_uvm_test_vector.txt'
    if os.path.exists(hmac224_file):
        generate_expected_hmac224_tag()
    if os.path.exists(hmac256_file):
        generate_expected_hmac256_tag()


main()
