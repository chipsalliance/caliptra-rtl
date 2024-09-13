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

def generate_expected_hmac384_tag():
    f = open("hmac384_uvm_test_vector.txt", "r")
    g = open("expected_hmac384_tag.txt", "w")
    h = open("expected_hmac384_tags_all.txt", "a")
    msg_str = ""
    key_str = ""
    seed_str = ""
    tag_str = ""

    for line in f:
        if(line[0:6] == "KEY = "):
            key_str = line.strip()[6:]  
        elif(line[0:7] == "SEED = "):
            seed_str = line.strip()[7:]   
        else:
            msg_str = msg_str + line.strip()[8:]

    #Generate digest using OpenSSL HMAC SHA384
    command = 'echo '+msg_str+' | xxd -r -p | openssl dgst -sha384 -mac hmac -macopt hexkey:'+key_str+' -hex'
    tag = subprocess.check_output(command, shell=True)
    tag_str = str(tag)

    #Chomp extra chars at beginning and end if python 3.6.8 is loaded
    if tag_str[1] == "'":
        tag_str = tag_str[11:-3]
    else:
        tag_str = tag_str.rstrip()
        tag_str = tag_str[9:]
    g.write('TAG = '+tag_str+'\n')
    h.write('TAG = '+tag_str+'\n')
    h.write("------------------------\n")


    f.close()
    g.close()
    h.close()

def generate_expected_hmac512_tag():
    f = open("hmac512_uvm_test_vector.txt", "r")
    g = open("expected_hmac512_tag.txt", "w")
    h = open("expected_hmac512_tags_all.txt", "a")
    msg_str = ""
    key_str = ""
    seed_str = ""
    tag_str = ""

    for line in f:
        if(line[0:6] == "KEY = "):
            key_str = line.strip()[6:]  
        elif(line[0:7] == "SEED = "):
            seed_str = line.strip()[7:]   
        else:
            msg_str = msg_str + line.strip()[8:]

    #Generate digest using OpenSSL HMAC SHA384
    command = 'echo '+msg_str+' | xxd -r -p | openssl dgst -sha512 -mac hmac -macopt hexkey:'+key_str+' -hex'
    tag = subprocess.check_output(command, shell=True)
    tag_str = str(tag)

    #Chomp extra chars at beginning and end if python 3.6.8 is loaded
    if tag_str[1] == "'":
        tag_str = tag_str[11:-3]
    else:
        tag_str = tag_str.rstrip()
        tag_str = tag_str[9:]
    g.write('TAG = '+tag_str+'\n')
    h.write('TAG = '+tag_str+'\n')
    h.write("------------------------\n")


    f.close()
    g.close()
    h.close()


def main():
    hmac384_file= 'hmac384_uvm_test_vector.txt'
    hmac512_file= 'hmac512_uvm_test_vector.txt'
    if os.path.exists(hmac384_file):
        generate_expected_hmac384_tag()
    if os.path.exists(hmac512_file):
        generate_expected_hmac512_tag()
    #generate_test()g

main()
