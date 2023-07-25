// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

#include "datavault.h"


#ifdef DV_SMALLSET    // Smaller test set for DEBUG

widereg_t dv_regs [DV_PFX_COUNT] = {
    { "STICKYDATAVAULTCTRL",                 (uint32_t *) CLP_DV_REG_STICKYDATAVAULTCTRL_0,             2,  0x1,     0x0 }, //  0. (0x1001c000) 
    { "STICKY_DATA_VAULT_ENTRY_0",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_0,       3,  DV_ONES, 0x0 }, //  1. (0x1001c028) 
    { "STICKY_DATA_VAULT_ENTRY_1",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_0,       3,  DV_ONES, 0x0 }, //  2. (0x1001c058) 
    { "DATAVAULTCTRL",                       (uint32_t *) CLP_DV_REG_DATAVAULTCTRL_0,                   2,  0x0,     0x0 }, //  3. (0x1001c208) 
    { "DATA_VAULT_ENTRY_0",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_0_0,              3,  DV_ONES, 0x0 }, //  4. (0x1001c230) 
    { "DATA_VAULT_ENTRY_1",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_1_0,              3,  DV_ONES, 0x0 }, //  5. (0x1001c260) 
    { "LOCKABLE_SCRATCHREG_CTRL",            (uint32_t *) CLP_DV_REG_LOCKABLESCRATCHREGCTRL_0,          2,  0x0,     0x0 }, //  6. (0x1001c410)
    { "LOCKABLE_SCRATCHREG",                 (uint32_t *) CLP_DV_REG_LOCKABLESCRATCHREG_0,              2,  DV_ONES, 0x0 }, //  7. (0x1001c438) 
    { "STICKY_LOCKABLE_SCRATCHREGCTRL",      (uint32_t *) CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0,    2,  0x1,     0x0 }, //  8. (0x1001c480) 
    { "STICKY_LOCKABLE_SCRATCHREG",          (uint32_t *) CLP_DV_REG_STICKYLOCKABLESCRATCHREG_0,        2,  DV_ONES, 0x0 }  //  9. (0x1001c4a0) 
};

enum ctrl_index {CTRL1 = 0, CTRL2 = 3, CTRL3 = 6, CTRL4 = 8, IXNA = -1};

ctrl_reg_t dv_ctrl_regids [] = {
    // dv_regs[j][0] locks: dv_regs[j+1][0], dv_regs[j+1][1], dv_regs[j+1][2]
    // dv_regs[j][1] locks: dv_regs[j+2][1], dv_regs[j+2][2], dv_regs[j+2][2]
    // dv_regs[j][3] locks: dv_regs[j+3][1], dv_regs[j+3][2], dv_regs[j+3][2]
    // ...
    {CTRL1, STICKY_2D,      3, {CTRL1+1, CTRL1+2, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA}},      // 2 sets x 3 slots
    {CTRL2, NONSTICKY_2D,   3, {CTRL2+1, CTRL2+2, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA}},      // 2 sets x 3 slots

    // dv_regs[j][0] locks: dv_regs[j+1][0], dv_regs[j+1][1], dv_regs[j+1][2]
    {CTRL3, NONSTICKY_1D,   1, {CTRL3+1, CTRL3+1, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA}},      // 2 x 1 set x 1 slot 
    {CTRL4, STICKY_1D,      1, {CTRL4+1, CTRL4+1, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA, IXNA}}       // 2 x 1 set x 1 slot 
};

int lock_status_bitmap [DV_PFX_COUNT] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };  // each entry corresponds to a row in dv_regs


// Interpreting the tables above 
/*
    STICKYDATAVAULTCTRL[0] locks:                 
        STICKY_DATA_VAULT_ENTRY_0[0]
        STICKY_DATA_VAULT_ENTRY_0[1]
        STICKY_DATA_VAULT_ENTRY_0[2]

    STICKYDATAVAULTCTRL[1] locks:                 
        STICKY_DATA_VAULT_ENTRY_1[0]
        STICKY_DATA_VAULT_ENTRY_1[1]
        STICKY_DATA_VAULT_ENTRY_1[2]
    --------------------------------------------------------------
    DATAVAULTCTRL[0] locks:       
        DATA_VAULT_ENTRY_0[0]
        DATA_VAULT_ENTRY_0[1]
        DATA_VAULT_ENTRY_0[2]

    DATAVAULTCTRL[1] locks:       
        DATA_VAULT_ENTRY_1[0]
        DATA_VAULT_ENTRY_1[1]
        DATA_VAULT_ENTRY_1[2]
    --------------------------------------------------------------
    LOCKABLE_SCRATCHREG_CTRL[0] locks:  
        LOCKABLE_SCRATCHREG[0]

    LOCKABLE_SCRATCHREG_CTRL[1] locks:  
        LOCKABLE_SCRATCHREG[1]
    --------------------------------------------------------------
    STICKY_LOCKABLE_SCRATCHREG_CTRL[0] locks:
        STICKY_LOCKABLE_SCRATCHREG[0]

    STICKY_LOCKABLE_SCRATCHREG_CTRL[1] locks:
        STICKY_LOCKABLE_SCRATCHREG[1]
*/


#else               // Default larger set 

widereg_t dv_regs [DV_PFX_COUNT] = {
    { "STICKYDATAVAULTCTRL",                 (uint32_t *) CLP_DV_REG_STICKYDATAVAULTCTRL_0,             10,  0x1,     0x0 }, //  0. (0x1001c000) 
    { "STICKY_DATA_VAULT_ENTRY_0",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_0_0,       12,  DV_ONES, 0x0 }, //  1. (0x1001c028) 
    { "STICKY_DATA_VAULT_ENTRY_1",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_1_0,       12,  DV_ONES, 0x0 }, //  2. (0x1001c058) 
    { "STICKY_DATA_VAULT_ENTRY_2",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_2_0,       12,  DV_ONES, 0x0 }, //  3. (0x1001c088) 
    { "STICKY_DATA_VAULT_ENTRY_3",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_3_0,       12,  DV_ONES, 0x0 }, //  4. (0x1001c0b8) 
    { "STICKY_DATA_VAULT_ENTRY_4",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_4_0,       12,  DV_ONES, 0x0 }, //  5. (0x1001c0e8) 
    { "STICKY_DATA_VAULT_ENTRY_5",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_5_0,       12,  DV_ONES, 0x0 }, //  6. (0x1001c118) 
    { "STICKY_DATA_VAULT_ENTRY_6",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_6_0,       12,  DV_ONES, 0x0 }, //  7. (0x1001c148) 
    { "STICKY_DATA_VAULT_ENTRY_7",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_7_0,       12,  DV_ONES, 0x0 }, //  8. (0x1001c178) 
    { "STICKY_DATA_VAULT_ENTRY_8",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_8_0,       12,  DV_ONES, 0x0 }, //  9. (0x1001c1a8) 
    { "STICKY_DATA_VAULT_ENTRY_9",           (uint32_t *) CLP_DV_REG_STICKY_DATA_VAULT_ENTRY_9_0,       12,  DV_ONES, 0x0 }, // 10. (0x1001c1d8) 
    { "DATAVAULTCTRL",                       (uint32_t *) CLP_DV_REG_DATAVAULTCTRL_0,                   10,  0x0,     0x0 }, // 11. (0x1001c208) 
    { "DATA_VAULT_ENTRY_0",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_0_0,              12,  DV_ONES, 0x0 }, // 12. (0x1001c230) 
    { "DATA_VAULT_ENTRY_1",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_1_0,              12,  DV_ONES, 0x0 }, // 13. (0x1001c260) 
    { "DATA_VAULT_ENTRY_2",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_2_0,              12,  DV_ONES, 0x0 }, // 14. (0x1001c290) 
    { "DATA_VAULT_ENTRY_3",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_3_0,              12,  DV_ONES, 0x0 }, // 15. (0x1001c2c0) 
    { "DATA_VAULT_ENTRY_4",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_4_0,              12,  DV_ONES, 0x0 }, // 16. (0x1001c2f0) 
    { "DATA_VAULT_ENTRY_5",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_5_0,              12,  DV_ONES, 0x0 }, // 17. (0x1001c320) 
    { "DATA_VAULT_ENTRY_6",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_6_0,              12,  DV_ONES, 0x0 }, // 18. (0x1001c350) 
    { "DATA_VAULT_ENTRY_7",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_7_0,              12,  DV_ONES, 0x0 }, // 19. (0x1001c380) 
    { "DATA_VAULT_ENTRY_8",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_8_0,              12,  DV_ONES, 0x0 }, // 20. (0x1001c3b0) 
    { "DATA_VAULT_ENTRY_9",                  (uint32_t *) CLP_DV_REG_DATA_VAULT_ENTRY_9_0,              12,  DV_ONES, 0x0 }, // 21. (0x1001c3e0) 
    { "LOCKABLE_SCRATCHREG_CTRL",            (uint32_t *) CLP_DV_REG_LOCKABLESCRATCHREGCTRL_0,          10,  0x0,     0x0 }, // 22. (0x1001c410)
    { "LOCKABLE_SCRATCHREG",                 (uint32_t *) CLP_DV_REG_LOCKABLESCRATCHREG_0,              10,  DV_ONES, 0x0 }, // 23. (0x1001c438) 
    { "NONSTICKY_GENERIC_SCRATCHREG",        (uint32_t *) CLP_DV_REG_NONSTICKYGENERICSCRATCHREG_0,      8 ,  0x0,     0x0 }, // 24. (0x1001c460) 
    { "STICKY_LOCKABLE_SCRATCHREG_CTRL",     (uint32_t *) CLP_DV_REG_STICKYLOCKABLESCRATCHREGCTRL_0,    8 ,  0x1,     0x0 }, // 25. (0x1001c480) 
    { "STICKY_LOCKABLE_SCRATCHREG",          (uint32_t *) CLP_DV_REG_STICKYLOCKABLESCRATCHREG_0,        8 ,  DV_ONES, 0x0 }  // 26. (0x1001c4a0) 
};


enum ctrl_index {CTRL1 = 0, CTRL2 = 11, CTRL3 = 22, CTRL4 = 25, IXNA = -1};


ctrl_reg_t dv_ctrl_regids [] = {
    // dv_regs[j][0] locks: dv_regs[j+1][0], dv_regs[j+1][1], dv_regs[j+1][2]
    // dv_regs[j][1] locks: dv_regs[j+2][1], dv_regs[j+2][2], dv_regs[j+2][2]
    // dv_regs[j][3] locks: dv_regs[j+3][1], dv_regs[j+3][2], dv_regs[j+3][2]
    // ...
    {CTRL1,  STICKY_2D,     12,   {CTRL1+1, CTRL1+2, CTRL1+3, CTRL1+4, CTRL1+5, CTRL1+6, CTRL1+7, CTRL1+8, CTRL1+9, CTRL1+10}},  // 10 sets x 12 slots
    {CTRL2,  NONSTICKY_2D,  12,   {CTRL2+1, CTRL2+2, CTRL2+3, CTRL2+4, CTRL2+5, CTRL2+6, CTRL2+7, CTRL2+8, CTRL2+9, CTRL2+10}},  // 10 sets x 12 slots

    // dv_regs[j][0] locks: dv_regs[j+1][0], dv_regs[j+1][1], dv_regs[j+1][2]
    {CTRL3,  NONSTICKY_1D,  1,    {CTRL3+1, CTRL3+1, CTRL3+1, CTRL3+1, CTRL3+1, CTRL3+1, CTRL3+1, CTRL3+1, CTRL3+1, CTRL3+1}},  // 1 set x 1 slot x 10 time
    {CTRL4,  STICKY_1D,     1,    {CTRL4+1, CTRL4+1, CTRL4+1, CTRL4+1, CTRL4+1, CTRL4+1, CTRL4+1, CTRL4+1, IXNA,    IXNA}}   // 1 set x 1 slot x 8 time
};

int lock_status_bitmap [DV_PFX_COUNT] =    { 0, 0, 0, 0, 0, 0, 0, 0,
                                             0, 0, 0, 0, 0, 0, 0, 0,
                                             0, 0, 0, 0, 0, 0, 0, 0, 
                                             0, 0, 0 
};  // each entry corresponds to a row in dv_regs


#endif  // DV_SMALLSET



int is_ctrl_reg(widereg_t *dv_reg) {
    return (str_contains((*dv_reg).pfx, "CTRL"));
}


widereg_t *find_dv_reg(volatile uint32_t *reg_addr) {
    for (int i=1; i < DV_PFX_COUNT; i++) {
        if ((reg_addr >= dv_regs[i-1].addr) && (reg_addr < dv_regs[i].addr))
            return &dv_regs[i-1]; 
    }
    return &dv_regs[DV_PFX_COUNT-1];
}


widereg_t *find_dv_reg_by_pfx(char * c) {
    for (int i = 0; i < DV_PFX_COUNT; i++) {
        if (strstr(dv_regs[i].pfx, c))
            return &dv_regs[i];
    }
    return NULL;
}



int get_datset_len(ctrl_reg_t *dv_ctrl_ptr) {

    int *ptr = dv_ctrl_ptr->set; 

    for (int i = 0; i < 10; i++, ptr++) {
        if (*ptr < 0) 
            return i;
    }
    return 10;
}


void update_bitmap( int ix, int j ) {
    int curr = lock_status_bitmap[ix];
    lock_status_bitmap[ix] = curr | (1 << j); 
}


void print_bitmap() {
    VPRINTF (LOW, "-------------------------------\n");
    for (int i = 0; i < DV_PFX_COUNT; i++) 
        VPRINTF (LOW, "  %40s: 0x%-3x\n", dv_regs[i].pfx, lock_status_bitmap[i]);
    VPRINTF (LOW, "-------------------------------\n");
}




// -- Standard lib util functions --

int str_contains(char *b, char *a) {
    return (strstr(b, a) != NULL);
}


// Very simple shuffle of an array of integers 'ptr' of length 'N' in place 
void shuffle(int *ptr, int N) {
    int j, tmp;

    for (int i = 0; i < N; i++) {
        j = rand() % N; 
        tmp = ptr[i];
        ptr[i] = ptr[j]; 
        ptr[j] = tmp; 
    } 
}  
