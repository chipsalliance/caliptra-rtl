from my_functions import tvla_plots
from Montgomery_model import test
from Montgomery_model import MONT_MULT

#tvla_plots('C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project')


wd_sz = 32 # word size
#
# p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
# test(MONT_MULT(p, wd_sz))

q = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
test(MONT_MULT(q, wd_sz))




