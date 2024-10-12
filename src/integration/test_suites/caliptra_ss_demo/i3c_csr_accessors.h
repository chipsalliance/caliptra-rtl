// SPDX-License-Identifier: Apache-2.0

#ifndef I3C_CSR_ACCESSORS_H
#define I3C_CSR_ACCESSORS_H

#include "caliptra_reg.h"
#include "riscv_hw_if.h"

#define DCT_MEM_WIDTH 128
#define DCT_MEM_WIDTH_BYTE (DCT_MEM_WIDTH / 8)
#define DAT_MEM_WIDTH 64
#define DAT_MEM_WIDTH_BYTE (DAT_MEM_WIDTH / 8)
#define REG_WIDTH 32
#define ADDR_INCR 4
#define DAT_REG_WSIZE (2)
#define DCT_REG_WSIZE (4)


/*  Checks if given buffer is initialized and if size is sufficient

    Arguments:
    * buf - pointer to the buffer
    * size - size of the buffer
    * min_size - minimum size of the buffer
*/
int is_buf_valid(uint32_t *buf, uint32_t size, uint32_t min_size) {
    if (size < min_size) {
        printf("ERROR: Buffer should have size higher than %d\n", min_size);
        return 0;
    }

    if (buf == 0) {
        printf("ERROR: Buffer must be initialized\n");
        return 0;
    }

    return 1;
}

/*  Writes value to memory at given address

    Arguments:
    * address - base address of the device that will be accessed on the bus
    * offset - offset of the register relative to base address
    * data - 32-bit value to write at calculated address
*/
void write_reg(uint32_t address, uint32_t offset, uint32_t data) {
    lsu_write_32((address + offset), data);
}

/*  Reads value from memory at given address

    Arguments:
    * address - base address of the device that will be accessed on the bus
    * offset - offset of the register relative to base address

    Returns 32-bit value read at given address
*/
uint32_t read_reg(uint32_t address, uint32_t offset) {
    return lsu_read_32((address + offset));
}

/*  Writes a value to the register

    Arguments:
    * address - absolute address of the register file
    * offset - relative address of the register in register file
    * low_bit - index of the lowest bit of the modified field
    * mask - mask of the register field in the register (should be contiguous)
    * data - value that will be written to the register field
*/
void write_reg_field(uint32_t address, uint32_t offset, uint8_t low_bit, uint32_t mask, uint32_t data) {
    uint32_t value = read_reg(address, offset);

    // Clear field by setting masked bits to 0
    value &= ~mask;
    // Set new field value
    value |= (data << low_bit) & mask;

    // Write updated register value
    write_reg(address, offset, value);
}

/*  Reads a value from the register

    Arguments:
    * address - absolute address of the register file
    * offset - relative address of the register in register file
    * low_bit - index of the lowest bit of the accessed field
    * mask - mask of the register field in the register (should be contiguous)

    Returns a 32-bit value read from the register
*/
uint32_t read_reg_field(uint32_t address, uint32_t offset, uint8_t low_bit, uint32_t mask) {
    uint32_t value = read_reg(address, offset);

    // Clear field by setting masked bits to 0
    value &= mask;
    // Set new field value
    value >>= low_bit;

    // Write updated register value
    return value;
}


/*  Writes a value to the I3C register

    Arguments:
    * offset - relative address of the register in the I3C address space
    * data - 32-bit word to write into the register
*/
void write_i3c_reg(uint32_t offset, uint32_t data) {
    write_reg(CLP_I3C_REG_I3CBASE_START, offset, data);
};

/*  Reads a value from the I3C register

    Arguments:
    * offset - relative address of the register in the I3C address space

    Returns a 32-bit value read from the register
*/
uint32_t read_i3c_reg(uint32_t offset) {
    return read_reg(CLP_I3C_REG_I3CBASE_START, offset);
}

/*  Writes a value to the I3C register field

    Arguments:
    * offset - relative address of the register in the I3C address space
    * low_bit - index of the lowest bit of the accessed field
    * mask - mask of the register field in the register (should be contiguous)
    * data - 32-bit word to write into the register
*/
void write_i3c_reg_field(uint32_t offset, uint8_t low_bit, uint32_t mask, uint32_t data) {
    write_reg_field(CLP_I3C_REG_I3CBASE_START, offset, low_bit, mask, data);
}

/*  Reads a value from the I3C register field

    Arguments:
    * offset - relative address of the register in the I3C address space
    * low_bit - index of the lowest bit of the accessed field
    * mask - mask of the register field in the register (should be contiguous)

    Returns a 32-bit value read from the register
*/
uint32_t read_i3c_reg_field(uint32_t offset, uint8_t low_bit, uint32_t mask) {
    return read_reg_field(CLP_I3C_REG_I3CBASE_START, offset, low_bit, mask);
}


/*  Writes a value to the I3C DAT table entry

    Arguments:
    * index - index of the accessed DAT table entry
    * data - 64-bit word to write into the DAT entry
*/
void write_dat_reg(uint8_t index, uint32_t *buf, uint32_t size) {
    if (!is_buf_valid(buf, size, DAT_REG_WSIZE))
        printf("%c", 0x1);

    write_reg(I3C_REG_DAT_MEMORY, index * DAT_MEM_WIDTH_BYTE, buf[0]);
    write_reg(I3C_REG_DAT_MEMORY, index * DAT_MEM_WIDTH_BYTE + 4, buf[1]);
}

/*  Reads a value from the I3C DAT table entry

    The value read from the register will be saved in the memory at the address provided
    in `buf` argument. This function assumes that the buffer points to the memory which
    is accessible at least two 32-bit words. Providing an address that does not suffice
    these requirements will result in undefined behavior.

    Arguments:
    * index - index of the accessed DAT table entry
    * buf - pointer to 32-bit buffer
*/
void read_dat_reg(uint8_t index, uint32_t *buf, uint32_t size) {
    if (!is_buf_valid(buf, size, DAT_REG_WSIZE))
        printf("%c", 0x1);

    for (int i = 0; i < DAT_REG_WSIZE; i++) {
        buf[i] = read_reg(I3C_REG_DAT_MEMORY, index * DAT_MEM_WIDTH_BYTE + i * 4);
    }
}

/*  Writes a value to the I3C DAT table entry field

    Arguments:
    * index - index of the accessed DAT table entry
    * low_bit - index of the lowest bit of the accessed field
    * mask - mask of the field in the DAT register, it should be contiguous and should
             cover the register as it was 32-bit wide, e.g. mask 0xffff0000000000
             should be provided as 0xffff00 (last 32 bits trimmed)
    * data - 32-bit word to write into the DAT entry
*/
void write_dat_reg_field(uint8_t index, uint8_t low_bit, uint32_t mask, uint32_t data) {
    uint32_t w_index = low_bit / REG_WIDTH * ADDR_INCR;
    uint8_t w_low_bit = low_bit % REG_WIDTH;
    write_reg_field(I3C_REG_DAT_MEMORY, (index * DAT_MEM_WIDTH_BYTE) + w_index, w_low_bit, mask, data);
}

/*  Reads a value from the I3C DAT table entry field

    Arguments:
    * index - index of the accessed DAT table entry
    * low_bit - index of the lowest bit of the accessed field
    * mask - mask of the field in the DAT register, it should be contiguous and should
             cover the register as it was 32-bit wide, e.g. mask 0xffff0000000000
             should be provided as 0xffff00 (last 32 bits trimmed)

    Returns a 32-bit value read from the entry field
*/
uint32_t read_dat_reg_field(uint8_t index, uint8_t low_bit, uint32_t mask) {
    uint32_t w_index = low_bit / REG_WIDTH * ADDR_INCR;
    uint8_t w_low_bit = low_bit % REG_WIDTH;
    return read_reg_field(I3C_REG_DAT_MEMORY, (index * DAT_MEM_WIDTH_BYTE) + w_index, w_low_bit, mask);
}


/*  Reads a value from the I3C DCT table entry

    The value read from the register will be saved in the memory at the address provided
    in `buf` argument. This function assumes that the buffer points to the memory which
    is accessible at least four 32-bit words. Providing an address that does not suffice
    these requirements will result in undefined behavior.

    Arguments:
    * index - index of the accessed DCT table entry
    * buf - pointer to 32-bit buffer
*/
void read_dct_reg(uint8_t index, uint32_t *buf, uint32_t size) {
    if (!is_buf_valid(buf, size, DCT_REG_WSIZE))
        printf("%c", 0x1);

    for (int i = 0; i < DCT_REG_WSIZE; i++) {
        buf[i] = read_reg(I3C_REG_DCT_MEMORY, index * DCT_MEM_WIDTH_BYTE + i * 4);
    }
}

/*  Reads a value from the I3C DCT table entry field

    Arguments:
    * index - index of the accessed DCT table entry
    * low_bit - index of the lowest bit of the accessed field
    * mask - mask of the field in the DCT register, it should be contiguous and should
             cover the register as it was 32-bit wide, e.g. mask 0xffff0000000000
             should be provided as 0xffff00 (last 32 bits trimmed)

    Returns a 32-bit value read from the entry field
*/
uint32_t read_dct_reg_field(uint8_t index, uint8_t low_bit, uint32_t mask) {
    uint32_t w_index = low_bit / REG_WIDTH * ADDR_INCR;
    uint8_t w_low_bit = low_bit % REG_WIDTH;
    return read_reg_field(I3C_REG_DCT_MEMORY, (index * DCT_MEM_WIDTH_BYTE), low_bit, mask);
}

#endif
