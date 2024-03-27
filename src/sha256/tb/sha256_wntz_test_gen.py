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
import sys
import secrets

def generate_expected_wntz_digest(w, n):
    print("w = ", w, "n = ", n)
    g = open("sha256_wntz_test_vector.txt", "w")
    h = open("sha256_wntz_test_vectors_all.txt", "a")
    h.write('w = '+str(w)+' n = '+str(n)+'\n')
    
    msg = ""
    msg_str = ""
    digest_str = ""
    msg_str_for_chain = ""  

    #------------------------------------------------------------------------
    #Generate random message of 256-bit or 192-bit length (based on n)
    if n == 1:
        num = 32
    else:
        num = 24
    
    #Replace j value with something < upper bound of Winternitz chain so error intr is not asserted - only for tb purposes
    j_rand = random.randint(0,(2**w)-2)
    j_rand = format(int(j_rand), '02x')
    # print(j_rand, type(j_rand))
    
    #Generate random message
    command = 'openssl rand -hex '+ str(num)
    msg = subprocess.check_output(command, shell=True)
    # print(msg, type(msg))
    msg_str_temp = str(msg)
    # print(msg_str_temp)

    #Replace j value of msg with the generated one that ensures it's within 2**w-2 upper bound
    msg_str = msg_str_temp[0:46] + j_rand + msg_str_temp[48:]
    # print(msg_str)

    #Chomp extra chars at beginning and end if python 3.6.8 is loaded
    if msg_str[1] == "'":
        msg_str = msg_str[2:-3]
    else:
        msg_str = msg_str.rstrip()
    # print("msg = "+msg_str+'\n'+"msg len = "+str(len(msg_str)*4))
    h.write("MSG = " + msg_str + '\n')

    #------------------------------------
    #Create a padded version of msg to write to file. This will be used to drive SHA BLOCK reg in tb
    if len(msg_str) < 128:
        pad_len = 128 - len(msg_str) - 2 - 16 #-2 to account for 'h80 to be placed at the end of msg while padding, -16 to account for msg len at the end
        msg_str_padded = msg_str + '80' + str(0)*pad_len + str(format(len(msg_str)*4, '016x'))
        # print("msg padded = " + msg_str_padded)
        if len(msg_str_padded) > 128:
            print("ERROR! check msg padding\n")
        g.write(msg_str_padded + '\n')
        h.write("MSG PADDED = " + msg_str_padded + '\n')

    #------------------------------------
    #Process msg input for subseq iterations of Wntz chain
    #This will be msg + j + digest. j and digest are appended later
    msg_str_for_chain = msg_str[0:44]
    # print("msg_str_for_chain = "+msg_str_for_chain)
    # print("j = ", msg_str[45:46], msg_str[44:46])
    if len(msg_str) > 46:
        j_init = int(msg_str[44:46], 16)
    else:
        j_init = 0

    # print("j_init = ", j_init,"msg_str[45:46] = ", msg_str[45:46])
    #------------------------------------------------------------------------

    #Generate 1st digest using OpenSSL sha256
    command = 'echo '+msg_str+' | xxd -r -p | openssl dgst -sha256'
    digest = subprocess.check_output(command, shell=True)
    digest_str = str(digest)

    #Chomp extra chars at beginning and end if python 3.6.8 is loaded
    if digest_str[1] == "'":
        digest_str = digest_str[11:-3]
    else:
        digest_str = digest_str.rstrip()
        digest_str = digest_str[9:]

    h.write('DIGEST_0 = '+digest_str+'\n')

    #Truncate digest to 192 bits in n = 0 mode
    if n == 0:
        digest_str = digest_str[0:48]

    # print("digest0 = " + digest_str)

    #Calculate chain of hashes for wntz
    for j in range(j_init,(2**w) - 2):
        #Generate digest using OpenSSL HMAC SHA384
        # print(str(j) + ":" + digest_str)
        digest_str = msg_str_for_chain+str(format(j+1,'02x'))+digest_str #+padding
        # print(str(j) + ":" +digest_str)
        command = 'echo '+digest_str+' | xxd -r -p | openssl dgst -sha256'
        digest = subprocess.check_output(command, shell=True)
        digest_str = str(digest)

        #Chomp extra chars at beginning and end if python 3.6.8 is loaded
        if digest_str[1] == "'":
            digest_str = digest_str[11:-3]
        else:
            digest_str = digest_str.rstrip()
            digest_str = digest_str[9:]

        #Truncate digest to 192 bits in n = 0 mode and feed to next iteration
        if n == 0:
            digest_str = digest_str[0:48]

    #Truncate last digest to 192 bits in n = 0 mode
    if n == 0:
        digest_str = digest_str[0:48] + str(0)*16

    g.write(digest_str+'\n')
    h.write('DIGEST_FINAL = '+digest_str+'\n')
    h.write("------------------------\n")

    # print("digest_str = "+digest_str)


    g.close()
    h.close()

def main():
    w_main = sys.argv[1];
    n_main = sys.argv[2];
    
    generate_expected_wntz_digest(int(w_main), int(n_main))

main()
