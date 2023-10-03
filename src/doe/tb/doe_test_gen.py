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
#
# This script generates:
# UDS, key, IV, ciphertext
# FE, key, IV, ciphertext
#********************************************************************************
import os
import subprocess
import re
import random
import secrets
from pathlib import Path

def encrypt(plaintext_filename, key_str, iv_str):
    #Encrypt UDS (to be used to drive DOE)
    command = 'cat '+ plaintext_filename +' | xxd -r -ps | openssl enc -aes-256-cbc -e -out temp -K ' + key_str + ' -iv ' + iv_str + ' -nopad'
    subprocess.run(command, shell=True)
    command = 'xxd -p -c 1000 temp'
    encrypted = subprocess.check_output(command, shell=True)
    cipher_str = str(encrypted)[2:-3] #Chomp extra chars and convert to string
    return cipher_str

def decrypt_and_compare(ciphertext_filename, key_str, iv_str, plain_str, flow):
    #Decrypt previous (this step is only to make sure openssl command is working)
    command = 'cat ' + ciphertext_filename + ' | xxd -r -ps | openssl enc -aes-256-cbc -d -out temp -K ' + key_str + ' -iv ' + iv_str + ' -nopad'
    subprocess.run(command, shell=True)
    command = 'xxd -p -c 1000 temp'
    decrypted = subprocess.check_output(command, shell=True)
    decrypted_str = str(decrypted)[2:-3]

    #Compare decrypted and plaintext to make sure they're matching
    if decrypted_str != plain_str:
        print(decrypted_str+'\n'+plain_str)
        print("Plaintext mismatch when decrypting " + flow + "! Check openssl command\n")

def generate_rand_bytes(num_bytes): #(key_bytes, iv_bytes, plaintext_bytes):
    #Generate 256-bit OBF KEY - UDS
    #key_str = str(secrets.token_hex(key_bytes)) #OBF KEY - 256 bit

    #Generate 128-bit IV
    #iv_str = str(secrets.token_hex(iv_bytes)) #IV - 128 bit

    #Generate 384-bit UDS (plaintext)
    #plain_str = str(secrets.token_hex(plaintext_bytes)) #UDS - 384 bit (12 dwords)
    #return key_str, iv_str, plain_str
    rand_str = str(secrets.token_hex(num_bytes))
    return rand_str


def generate_doe_testvector():
    f = open("doe_test_vector.txt", "w")
    g = open("doe_test_vectors_all.txt", "a")
    
    #-------------------------------------
    #UDS
    #-------------------------------------
    p = open("uds", "w")
    c = open("ciphertext", "w")

    #key_str, iv_str, plain_str = generate_rand_bytes(32, 16, 48)
    key_str     = generate_rand_bytes(32)
    iv_str      = generate_rand_bytes(16)
    plain_str   = generate_rand_bytes(48)
    # key_str = "002ec695b21f27581a745c72e5b9f484865bc95eb10a13d584f57062166838d6"
    # iv_str = "a07b6cf2c26e78194b698f30ed0f5bdb"
    # plain_str = "754e68e5bdb5df41fca420e77655c76fe8ac8e4bc55727b2132bfdf9419a3b21b0dcc413c6f3f64a9b2d6cc1d861065b"
    p.write(plain_str)
    p.close()

    #Encrypt plaintext
    cipher_str = encrypt("uds", key_str, iv_str)
    c.write(cipher_str)
    c.close()

    #Decrypt ciphertext and make sure it matches with generated plaintext
    decrypt_and_compare("ciphertext", key_str, iv_str, plain_str, "UDS")
    

    #Write all values to a file to be used in test
    f.write(key_str+'\n'+iv_str+'\n'+plain_str+'\n'+cipher_str+'\n')
    g.write("OBF UDS key: "+key_str+'\n'+ "IV: "+iv_str+'\n'+ "UDS plaintext: "+plain_str+'\n'+ "UDS ciphertext: "+cipher_str+'\n')

    #-------------------------------------
    #FE
    #-------------------------------------
    p = open("fe", "w")
    c = open("ciphertext", "w")
    
    plain_str = "" #Clear out plain str
    #iv_str, plain_str = generate_rand_bytes(16, 32) #Use same key as UDS
    iv_str      = generate_rand_bytes(16)
    plain_str   = generate_rand_bytes(32)
    p.write(plain_str)
    p.close()

    #Encrypt plaintext
    cipher_str = encrypt("fe", key_str, iv_str)
    c.write(cipher_str)
    c.close()

    #Decrypt ciphertext and make sure it matches with generated plaintext
    decrypt_and_compare("ciphertext", key_str, iv_str, plain_str, "FE")
    

    #Write all values to a file to be used in test
    f.write(key_str+'\n'+iv_str+'\n'+plain_str+'\n'+cipher_str+'\n')
    g.write("OBF FE key: "+key_str+'\n'+"IV: "+iv_str+'\n'+"FE plaintext: "+plain_str+'\n'+"FE ciphertext: "+cipher_str+'\n')

    g.write('---------------------------------\n')
    f.close()
    g.close()

    #Temp file clean up
    os.remove("uds")
    os.remove("fe")
    os.remove("ciphertext")
    os.remove("temp")

def main():
    generate_doe_testvector()

main()
    