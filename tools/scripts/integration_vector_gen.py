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
import numpy
import argparse
from textwrap import wrap

def generate_vector_file_sha512(src_dir, dest_dir, dest_name, arg_f):

    for src_name in arg_f:

        # open source vector file and read in lines
        src_file = open(src_dir+src_name,'r')
        src_lines = src_file.readlines()
        src_file.close()

        # open destination file and check if vectors section is already generated
        empty_file = False
        keyword_found = False
        keyword = src_name[:-4]
        print("keyword is: ",keyword)

        try:
            dest_file = open(dest_dir+dest_name,"r+")
            dest_lines = dest_file.readlines()
        except:
            dest_file = open(dest_dir+dest_name,"w")
            empty_file = True

        if empty_file == False:
            for line in dest_lines:
                if keyword in line:
                    keyword_found = True

        if keyword_found == True:
            print("vectors already exist: ", keyword)
            continue

        # process the source vector file and write to new files
        if empty_file == True:
            dest_file.write(".data\n")
        dest_file.write(keyword+':\n')

        vector_cnt = 0
        for line in src_lines:
            # write length
            if 'Len = ' in line:
                vector_cnt = vector_cnt + 1
                dest_file.write("// " + keyword + "vector_" + str(vector_cnt) + "\n")
                dest_file.write("// vector length\n")

                msg_len_int = int(line[6:])
                dest_file.write(".word " + ("0x%08X" % msg_len_int) + "\n")

            # write message
            if 'Msg = ' in line:
                dest_file.write("// input message\n")
                msg = line[6:]
                msg_wrapped = wrap(msg,8)
                # add padding
                if len(msg_wrapped[-1]) < 8:
                    msg_wrapped[-1] = msg_wrapped[-1] + '8' + (8-len(msg_wrapped[-1])-1)*'0'
                else:
                    msg_wrapped.append("80000000")

                for word in msg_wrapped:
                    dest_file.write(".word 0x" + word + "\n")
                remain_word = 32 - len(msg_wrapped) % 32;
                if remain_word < 4: remain_word = remain_word + 128

                for i in range(remain_word - 4):
                    dest_file.write(".word 0x00000000\n")

                # append message length info at the back
                msg_len_append = "0x%032X" % msg_len_int
                msg_len_append = wrap(msg_len_append[2:], 8)
                for word in msg_len_append:
                    dest_file.write(".word 0x" + word + "\n")

            # write expected
            if 'MD = ' in line:
                dest_file.write("// expected output\n")
                expected = line[5:]
                expected_wrapped = wrap(expected,8)
                for word in expected_wrapped:
                    dest_file.write(".word 0x" + word + "\n")

                for i in range(16 - len(expected_wrapped)):
                    dest_file.write(".word 0x00000000\n")

    pass


def generate_vector_file_aes(src_dir, dest_dir, dest_name, arg_f):

    for src_name in arg_f:

        # open source vector file and read in lines
        src_file = open(src_dir+src_name,'r')
        src_lines = src_file.readlines()
        src_file.close()

        # open destination file and check if vectors section is already generated
        empty_file = False
        keyword_found = False
        keyword = src_name[:-4]
        print("keyword is: ",keyword)

        try:
            dest_file = open(dest_dir+dest_name,"r+")
            dest_lines = dest_file.readlines()
        except:
            dest_file = open(dest_dir+dest_name,"w")
            empty_file = True

        if empty_file == False:
            for line in dest_lines:
                if keyword in line:
                    keyword_found = True

        if keyword_found == True:
            print("vectors already exist: ", keyword)
            continue

        # process the source vector file and write to new files
        if empty_file == True:
            dest_file.write(".data\n")
        dest_file.write(keyword+':\n')

        vector_cnt = 0
        for line in src_lines:
            # define operation mode:
            if '[ENCRYPT]' in line:
                op_mode = 1
            elif '[DECRYPT]' in line:
                op_mode = 0

            # get key
            if 'KEY = ' in line:
                vector_cnt = vector_cnt + 1
                key = line[6:-1]
                key_wrapped = wrap(key,8)

            # get IV
            if 'IV' in line:

                IV = line[5:]
                IV_wrapped = wrap(IV,8)

            # get message
            if 'PLAINTEXT = ' in line:
                msg = line[12:]
                msg_wrapped = wrap(msg,8)

            # get expected
            if 'CIPHERTEXT ='  in line:
                expected = line[13:]
                expected_wrapped = wrap(expected,8)

                # write information
                dest_file.write("// " + keyword + "_vector" + str(vector_cnt) + "\n")
                key_len_int = int(len(key)/32)
                msg_len_int = int(len(msg)/32)
                config_int = int((key_len_int-1) * 2 + op_mode)
                dest_file.write("// indicates op mode and key length, write to AES_ADDR_CONFIG\n")
                dest_file.write(".word " + ("0x%08X" % config_int) + "\n")
                dest_file.write("// indicates message length, multiply of 128\n")
                dest_file.write(".word " + ("0x%08X" % msg_len_int) + "\n")
                #write key
                dest_file.write("// start of key\n")
                for key_word in key_wrapped:
                    dest_file.write(".word 0x" + key_word + "\n")
                # write IV
                dest_file.write("// start of IV\n")
                for IV_word in IV_wrapped:
                    dest_file.write(".word 0x" + IV_word + "\n")
                # write message
                dest_file.write("// input message\n")
                for msg_word in msg_wrapped:
                        dest_file.write(".word 0x" + msg_word + "\n")
                # write expected
                dest_file.write("// expected output\n")
                for word in expected_wrapped:
                    dest_file.write(".word 0x" + word + "\n")

    pass

class Argument_Defaults:
    algorithms = "sha512"
    filenames = ""


class HelpMessage:
    algorithms = (
        ''' the type of crypto algorithm "'''
        + Argument_Defaults.algorithms
        + """."""
    )
    filenames = (
        ''' the filenames of the vector files "'''
        + Argument_Defaults.filenames
        + """."""
    )

if __name__ == '__main__':

    parser = argparse.ArgumentParser(prog="vector_gen", description="add vector files here")
    parser.add_argument(
        "-a", type=str, help=HelpMessage.algorithms, default=Argument_Defaults.algorithms, choices=['sha512', 'aes']
    )
    parser.add_argument(
        "-f", type=str, help=HelpMessage.filenames, default=Argument_Defaults.filenames, nargs = '*'
    )
    args = parser.parse_args()

    if (args.a == 'sha512'):
        src_dir = '../../sha512/tb/vectors/'
        dest_dir = './smoke_test_sha512/'
        dest_filename = 'smoke_test_sha512_vectors.s'
        generate_vector_file_sha512(src_dir, dest_dir, dest_filename, args.f)
    elif (args.a == 'aes'):
        src_dir = '../../aes/tb/vectors/'
        dest_dir = './smoke_test_aes/'
        dest_filename = 'smoke_test_aes_vectors.s'
        generate_vector_file_aes(src_dir, dest_dir, dest_filename, args.f)
