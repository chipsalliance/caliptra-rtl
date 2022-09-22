import random
import pandas as pd
import numpy as np
import os
from matplotlib import pyplot as plt
import string
from PRNG import XorShiftRng


def protected_modular_arithmetic_operation(q=137, privKey=75, r=45, h=128, k_inv=45, RRNG=XorShiftRng(1), PRNG_off=0):
    d1 = RRNG.XorShift_PRNG() & 0x3FFFFFF
    d1 = reduction(d1)
    if PRNG_off == 1:
        d1 = 5
    if (privKey - d1) >= 0:
        P1_2 = reduction(privKey - d1)
    else:
        P1_2 = reduction(privKey - d1 + q)
    P1 = P1_2
    P2 = d1
    PR1 = reduction(P1 * r)
    PR2 = reduction(P2 * r)
    d2 = RRNG.XorShift_PRNG() & 0x3FFFFFF
    d2 = reduction(d2)
    if PRNG_off == 1:
        d2 = 5
    if (PR1 + h - d2) >= 0:
        PRH1_2 = reduction(PR1 + h - d2)
    else:
        PRH1_2 = reduction(PR1 + h - d2 + q)
    PRH1 = PRH1_2
    PRH2 = reduction(PR2 + d2)
    s1 = reduction(PRH1 * k_inv)
    s2 = reduction(PRH2 * k_inv)
    s = reduction(s1 + s2)
    comb = np.array([P1, P2, PR1, PR2, PRH1, PRH2, s1, s2], dtype=np.int32)
    return s, comb


def unprotected_modular_arithmetic_operation(q=137, privKey=75, r=45, h=128, k_inv=45):
    PR = (privKey * r) % q
    PRH = (PR + h) % q
    s = (PRH * k_inv) % q
    comb = np.array([PR, PRH], dtype=np.int32)
    return s, comb


def verify_masking(q=137, itr=10):
    k_inv = random.randint(1, q - 1)
    privKey = random.randint(1, q - 1)
    for i in range(0, itr):
        h = random.randint(0, q - 1)
        r = random.randint(0, q - 1)
        result1, column1 = protected_modular_arithmetic_operation(q=q, privKey=privKey, r=r, h=h, k_inv=k_inv)
        result2, column2 = unprotected_modular_arithmetic_operation(q=q, privKey=privKey, r=r, h=h, k_inv=k_inv)
        new_col = np.concatenate((column1, column2), axis=0)
        if result1 != result2:
            print(f'error {result1} and {result2}')
            result1, column1 = protected_modular_arithmetic_operation(q=q, privKey=privKey, r=r, h=h, k_inv=k_inv)
            return 0

    print('TEST PASSED')
    return 1


def testing_masking(q=137, itr=10, RRNG=XorShiftRng(1), bar=1, directory='C:/Users/t-ekarabulut/OneDrive - '
                                                                         'Microsoft/Caliptra_masked_arith/math_model/results'):
    k_inv = random.randint(1, q - 1)
    privKey = random.randint(1, q - 1)
    h = random.randint(0, q - 1)
    r = random.randint(0, q - 1)
    result = np.zeros((itr, 8), dtype=np.int32)
    for i in range(0, itr):
        result1, column1 = protected_modular_arithmetic_operation(q=q, privKey=privKey, r=r, h=h, k_inv=k_inv,
                                                                  RRNG=RRNG)
        result[i] = column1

    pd.DataFrame(result).to_csv(os.path.join(directory, f'./mask_result.csv'))
    if bar == 1:
        bins = np.arange(start=0, stop=q + 1, step=1)
        for k in range(1, 9):
            a = result[:, k - 1].T
            N, bins, patches = plt.hist(a, bins=bins, edgecolor='black')
            for i in range(len(N)):
                patches[i].set_facecolor("#" + ''.join(random.choices("ABCDEF" + string.digits, k=6)))
            plt.title("histogram")
            plt.savefig(os.path.join(directory, f'./mask_result_{k}_hist.png'))
            plt.close()
    else:
        for k in range(1, 9):
            a = result[:, k - 1].T
            hist, bin_edges, patches = plt.hist(a, bins=50, density=False)
            bin_center = (bin_edges[:-1] + bin_edges[1:]) / 2
            plt.figure()
            plt.title("histogram")
            plt.hist(a, bins=50, density=False, histtype='step')
            plt.errorbar(bin_center, hist, yerr=50, fmt='.')
            plt.savefig(os.path.join(directory, f'./mask_result_{k}_hist.png'))
            plt.close()

    print('TEST PASSED')
    return 1


# The prime number is 8191 = 2^13 -1 = 0x1FFF
def reduction(x):
    # if x < 0:
    #     x = x + 0x1FFF
    # else:
    #     x = x + 0
    x = np.uint32(x)
    MSB = (x >> 13) & 0x1FFF
    LSB = x & 0x1FFF
    y = MSB + LSB
    MSB = (y >> 13) & 0x1FFF
    LSB = y & 0x1FFF
    y = MSB + LSB
    if y == 0x1FFF:
        return 0
    else:
        return y


def verify_reduction(itr=10):
    for i in range(0, itr):
        input = random.randint(0, 67108863)  # 67108863= 0x3FFFFFF
        result1 = reduction(input)
        result2 = input % 8191
        if result1 != result2:
            print(f'error {result1} and {result2}')
            result1 = reduction(input)
            return 0

    print('TEST PASSED')
    return 1
