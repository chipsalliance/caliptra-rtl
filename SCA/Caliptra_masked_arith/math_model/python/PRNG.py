import numpy as np


class XorShiftRng(object):
    def __init__(self, x):
        self.x = np.uint64(x)

    def XorShift_PRNG(self):
        self.x ^= self.x << np.uint64(21)
        self.x ^= self.x >> np.uint64(35)
        self.x ^= self.x << np.uint64(4)
        return np.int64(self.x)
