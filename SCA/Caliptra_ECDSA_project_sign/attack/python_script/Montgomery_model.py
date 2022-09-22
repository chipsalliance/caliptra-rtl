# Montgomery Multiplier parameter
import math
import random
import csv
import binascii


class MONT_MULT():
    def __init__(self, p, wd_sz):
        digit_no, fd_sz, R2, mu_word, prime_word = set_Mont_parameter(p, wd_sz)
        self.p = p
        self.wd_sz = wd_sz
        self.digit_no = digit_no
        self.fd_sz = fd_sz
        self.R2 = R2
        self.mu_word = mu_word
        print("mu_word = ", hex(mu_word))
        self.prime_word = prime_word
        self.Mask = 2 ** wd_sz - 1


def conv2digit(x, digit_size, digit_no):
    t = x
    T = []
    for i in range(digit_no):
        T.append(0)
    i = 0
    while t > 0:
        T[i] = t & (2 ** digit_size - 1)
        t = t >> digit_size;
        i += 1
    return T


def egcd(a, b):
    if a == 0:
        return b, 0, 1
    else:
        g, y, x = egcd(b % a, a)
        return g, x - (b // a) * y, y


def modinv(a, m):
    g, x, y = egcd(a, m)
    if g != 1:
        raise Exception('modular inverse does not exist')
    else:
        return x % m


def set_Mont_parameter(prime, wd_sz):
    digit_no = math.ceil((len(bin(prime)) - 2) / wd_sz) + 1  # number of words

    fd_sz = wd_sz * digit_no  # feild size
    R = 2 ** wd_sz
    R2 = (2 ** fd_sz) ** 2 % prime
    mu_word = (-modinv(prime, R)) % R

    prime_word = {}
    for i in range(digit_no):
        prime_word[i] = (prime >> wd_sz * i) % R

    return digit_no, fd_sz, R2, mu_word, prime_word


def sum_carry(x, wd_sz):
    S = x & (2 ** wd_sz - 1)
    C = x >> wd_sz
    return (C, S)


def Mont_mult(X, Y, mont_mult):
    X_ = conv2digit(X, mont_mult.wd_sz, mont_mult.digit_no + 1)
    Y_ = conv2digit(Y, mont_mult.wd_sz, mont_mult.digit_no + 1)
    T = conv2digit(0, mont_mult.wd_sz, mont_mult.digit_no + 1)
    for i in range(mont_mult.digit_no):
        (C1, S) = sum_carry(T[0] + (X_[i] * Y_[0]), mont_mult.wd_sz)
        m = (S * mont_mult.mu_word) & mont_mult.Mask
        (C, S) = sum_carry(S + m * mont_mult.prime_word[0], mont_mult.wd_sz)
        C = C + C1
        # C = C + S
        for j in range(1, mont_mult.digit_no):
            (C, S) = sum_carry(T[j] + m * mont_mult.prime_word[j] + X_[i] * Y_[j] + C, mont_mult.wd_sz)
            T[j - 1] = S
        T[mont_mult.digit_no - 1] = C & mont_mult.Mask

    T_total = 0
    for j in range(mont_mult.digit_no):
        T_total += (T[j] << j * mont_mult.wd_sz)
    return T_total


def test(mont_mult):
    test_round = 1000000
    error = 0
    with open(f'../../data/MM_vector.csv', 'w', encoding="ISO-8859-1", newline='') as file:
        write = csv.writer(file)
        for i in range(test_round):
            # generate two random values in the field
            x = random.randint(0, 2 * (mont_mult.p - 1))
            # y = random.randint(0, 2 * (mont_mult.p - 1))
            y = 0x119af062cd9c27756d955872095776726357d13239fe3053c9f1ab5d22e9f8b58834baa4c04af4a333eadf122cc0044ed

            # product in normal domain
            res_normal = x * y % mont_mult.p

            # convert the operand to Montgomery domain
            X = Mont_mult(x, mont_mult.R2, mont_mult)
            Y = Mont_mult(y, mont_mult.R2, mont_mult)
            plaintext = str(hex(X))
            plaintext = plaintext[2:]
            plaintext = plaintext.zfill(int(384 / 4))
            plaintext = bytes.fromhex(plaintext)

            # product in Montgomery domain
            XY = Mont_mult(X, Y, mont_mult)
            ciphertext = str(hex(XY))
            ciphertext = ciphertext[2:].zfill(int(384 / 4))
            ciphertext = bytes.fromhex(ciphertext)

            byt_combined = plaintext + ciphertext
            write.writerow(byt_combined)

            # convert product from Montgomery domain to normal domain
            res_mont = Mont_mult(XY, 1, mont_mult)

            # test comparison
            if res_normal != res_mont:
                error += 1
                print('Error for: \nx=', hex(x), '\ny=', hex(y))


    if (error == 0):
        print('TEST PASSED.')
    else:
        print('TEST FAILED.')
    return


