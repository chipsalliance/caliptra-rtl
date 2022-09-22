from my_functions import tvla_plots, CPA, HW_calculator
import numpy as np

#tvla_plots('C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project_sign')

# start_to_search = 10
# key_guess = start_to_search + 0
# inter_1 = np.int64(0xffb5b685 * 0x7b689417)
# MSB = np.int64((inter_1 >> 32) & 0xFFFFFFFF)
# LSB = np.int64(inter_1 & 0xFFFFFFFF)
# inter_2 = LSB + MSB
# print(HW_calculator(inter_2))


CPA('C:/Users/t-ekarabulut/OneDrive - Microsoft/Caliptra_ECDSA_project_sign', itr=10)


