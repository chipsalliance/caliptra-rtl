from math_functions import unprotected_modular_arithmetic_operation, protected_modular_arithmetic_operation
from math_functions import verify_masking, testing_masking, verify_reduction
import random
from PRNG import XorShiftRng

# verify_reduction(5000000)
rng = XorShiftRng(1)
# result = verify_masking(q=8191, itr=100000)
result = testing_masking(q=8191, itr=1000000, bar=1, RRNG=rng)

# for _ in range(16):
#     print(hex(rng.XorShift_PRNG()))
