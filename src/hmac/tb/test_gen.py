#/usr/local/bin/python3
import os
import subprocess
import random

def calc_pad_chars(num_bits, start_padding):
    pad_bits = (1024 - num_bits)
    pad_bytes = int((pad_bits / 8) - start_padding) #One byte for 'h80 at the start of padding or all 0s based on value of start_padding field
    pad_chars = pad_bytes*2
    return pad_chars

def calc_msg_len(total_num_bits):
    size_chars = 16*2 #16 bytes = 128 bits
    msg_len = str(hex(1024 + total_num_bits))
    msg_len = msg_len[2:]
    size_chars = size_chars - len(msg_len)
    msg_len = (str(0) * size_chars) + msg_len
    return msg_len

def generate_test():

    #Open file for logging outputs
    f = open("test_vector.txt", "w")
    g = open("ref_test_vector.txt", "a")

    #Generate 384-bit key
    key = subprocess.check_output('openssl rand -hex 48', shell=True)
    key_str = str(key)
    f.write('KEY = '+key_str[2:-3]+'\n')
    g.write('KEY = '+key_str[2:-3]+'\n')

    #Generate random length msg (upper limit of length is 512 bytes)
    num_bytes = random.randrange(1,512)
    command = 'openssl rand -hex '+str(num_bytes)
    msg = subprocess.check_output(command, shell=True)
    msg_str = str(msg)
    msg_str = msg_str[2:-3]
    orig_msg_str = msg_str

    #Post process msg to divide into 1024-bit blocks. Last runt msg will get padding + msg length
    #If msg length is <=895 bits, it will be single blk msg
    #If msg length is > 895, it will be multi blk msg
    num_bits = num_bytes * 8

    #Following cases are possible:
    #case 1: msg =  1200 bits --> 1024,  176 + pad + size
    #case 2: msg =  1024 bits --> 1024,  pad + size
    #case 3: msg =  1023 bits --> 1023 + pad,  pad + size
    #case 4: msg =  896  bits --> 896  + pad,  pad + size
    #case 5: msg <= 895  bits --> 895  + pad + size
    total_num_bits = num_bits
    zero = str(0)
    one  = str(80)
    while num_bits > 0:
        if num_bits > 1023: #case 1 and 2
            block = msg_str[0:256]
            f.write('BLOCK = '+block+'\n')
            g.write('BLOCK = '+block+'\n')
            msg_str = msg_str[256:]
            num_bits = num_bits - 1024


            #We know here that we don't have space for msg, pad AND msg length, so we just do msg + pad
            pad_chars = calc_pad_chars(num_bits, 1)
            pad = one + zero * pad_chars


        elif num_bits <= 895: #case 5
            pad_chars = calc_pad_chars(num_bits+128, 1) #pad chars = 1024 - (msg + msg_len bits)
        
            pad = one + zero * pad_chars
    
            msg_len = calc_msg_len(total_num_bits)
            num_bits = 0

            block = msg_str + pad + msg_len
            f.write('BLOCK = '+block+'\n')
            g.write('BLOCK = '+block+'\n')

        else: #case 3 and 4
            
            #We know here that we don't have space for msg, pad AND msg length, so we just do msg + pad
            pad_chars = calc_pad_chars(num_bits, 1)

            pad = one + zero * pad_chars
            block = msg_str + pad
            f.write('BLOCK = '+block+'\n')
            g.write('BLOCK = '+block+'\n')
            
            pad_chars = calc_pad_chars(128, 0) #No msg in this block. Only msg_len and padding is continued (all 0s in padding)
            pad = zero * pad_chars

            msg_len = calc_msg_len(total_num_bits)
            num_bits = 0

            block = pad + msg_len
            f.write('BLOCK = '+block+'\n')
            g.write('BLOCK = '+block+'\n')

            
    

    #Generate digest using OpenSSL HMAC SHA384
    command = 'echo '+orig_msg_str+' | xxd -r -p | openssl dgst -sha384 -mac hmac -macopt hexkey:'+key_str[2:-3]+' -hex'
    tag = subprocess.check_output(command, shell=True)
    tag_str = str(tag)
    f.write('TAG = '+tag_str[11:-3]+'\n')
    g.write('TAG = '+tag_str[11:-3]+'\n')

    #Close file
    f.close()
    g.write('\n')
    g.close()

generate_test()

