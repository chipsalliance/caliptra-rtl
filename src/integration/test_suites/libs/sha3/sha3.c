// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Taken from the KMAC DIF in OpenTitan:
// https://github.com/lowRISC/opentitan/blob/master/sw/device/lib/dif/dif_kmac.c

#include "sha3.h"
#include "printf.h"

/**
 * Calculate the rate (r) in bits from the given security level.
 *
 * @param security_level Security level in bits.
 * @returns Rate in bits.
 */
static uint32_t calculate_rate_bits(uint32_t security_level) {
  // Formula for the rate in bits is:
  //
  //   r = 1600 - c
  //
  // Where c is the capacity (the security level in bits multiplied by two).
  return 1600 - 2 * security_level;
}

void dif_kmac_poll_status(const uintptr_t kmac, uint32_t flag) {
  while (1) {
    uint32_t reg = lsu_read_32(kmac + KMAC_STATUS_REG_OFFSET);
    if (reg & (0x1u << flag)) {
      break;
    }
  }
  return;
}

void dif_kmac_mode_sha3_start(
    const uintptr_t kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_sha3_t mode) {
  if (kmac == 0 || operation_state == 0) {
    printf("dif_kmac_mode_sha3_start: ERROR kmac or operation_state NULL.\n");
    while(1);
    return;
  }

  // Set key strength and calculate rate (r) and digest length (d) in 32-bit
  // words.
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeSha3Len224:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224;
      operation_state->offset = 0;
      operation_state->r = calculate_rate_bits(224) / 32;
      operation_state->d = 224 / 32;
      break;
    case kDifKmacModeSha3Len256:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256;
      operation_state->offset = 0;
      operation_state->r = calculate_rate_bits(256) / 32;
      operation_state->d = 256 / 32;
      break;
    case kDifKmacModeSha3Len384:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L384;
      operation_state->offset = 0;
      operation_state->r = calculate_rate_bits(384) / 32;
      operation_state->d = 384 / 32;
      break;
    case kDifKmacModeSha3Len512:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L512;
      operation_state->offset = 0;
      operation_state->r = calculate_rate_bits(512) / 32;
      operation_state->d = 512 / 32;
      break;
    default:
      printf("dif_kmac_sha3_start: ERROR Unsupported mode.\n");
      while(1);
      return;
  }

  // Hardware must be idle to start an operation.
  uint32_t kmac_status = lsu_read_32(kmac + KMAC_STATUS_REG_OFFSET);
  if ((kmac_status & (0x1U << KMAC_STATUS_SHA3_IDLE_INDEX)) == 0) {
    printf("dif_kmac_sha3_start: ERROR hardware must be idle.\n");
    while(1);
    return;
  }

  operation_state->squeezing = false;
  operation_state->append_d = false;

  // Configure SHA-3 mode with the given strength.
  // Must be written twice because it is a shadow register.
  uint32_t config_reg = (kstrength << KMAC_CFG_SHADOWED_KSTRENGTH_INDEX) |
                        (KMAC_CFG_SHADOWED_MODE_VALUE_SHA3 << KMAC_CFG_SHADOWED_MODE_INDEX);
  lsu_write_32(kmac + KMAC_CFG_SHADOWED_REG_OFFSET, config_reg);
  lsu_write_32(kmac + KMAC_CFG_SHADOWED_REG_OFFSET, config_reg);
  config_reg = lsu_read_32(kmac + KMAC_CFG_SHADOWED_REG_OFFSET);

  // Issue start command.
  lsu_write_32(kmac + KMAC_CMD_REG_OFFSET,
               (KMAC_CMD_CMD_VALUE_START << KMAC_CMD_CMD_INDEX));

  // Poll until the status register is in the 'absorb' state.
  return dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_ABSORB_INDEX);
}

static void msg_fifo_write(
    const uintptr_t kmac, const unsigned char *data, size_t len) {
  // Copy message using aligned word sized loads and stores where possible to
  // improve performance. Note: the parts of the message copied a byte at a time
  // will not be byte swapped in big-endian mode.
  uint32_t *aligned_data;
  for (; len != 0 && ((uintptr_t)data) % sizeof(uint32_t); --len) {
    lsu_write_8(kmac + KMAC_MSG_FIFO_REG_OFFSET, *data++);
  }
  for (; len >= sizeof(uint32_t); len -= sizeof(uint32_t)) {
    aligned_data = (uint32_t *) data;
    lsu_write_32(kmac + KMAC_MSG_FIFO_REG_OFFSET,
                        *aligned_data);
    data += sizeof(uint32_t);
  }
  for (; len != 0; --len) {
    lsu_write_8(kmac + KMAC_MSG_FIFO_REG_OFFSET, *data++);
  }
}

void dif_kmac_absorb(
    const uintptr_t kmac, dif_kmac_operation_state_t *operation_state,
    const void *msg, size_t len, size_t *processed) {
  // Set the number of bytes processed to 0.
  if (processed != 0) {
    *processed = 0;
  }

  if (kmac == 0 || operation_state == 0 || (msg == 0 && len != 0)) {
    printf("dif_kmac_absorb: ERROR one of function arguments is null\n");
    while (1);
    return;
  }

  // Check that an operation has been started.
  if (operation_state->r == 0) {
    printf("dif_kmac_absorb: ERROR operation not started yet\n");
    while (1);
    return;
  }

  // Poll until the status register is in the 'absorb' state.
  uint32_t kmac_status = lsu_read_32(kmac + KMAC_STATUS_REG_OFFSET);
  if ((kmac_status & (0x1U << KMAC_STATUS_SHA3_ABSORB_INDEX)) == 0) {
    printf("dif_kmac_absorb: ERROR hardware must be absorbing.\n");
    while(1);
    return;
  }

  // Copy message using aligned word sized loads and stores where possible to
  // improve performance. Note: the parts of the message copied a byte at a time
  // will not be byte swapped in big-endian mode.
  const unsigned char *data = (const unsigned char *)msg;
  uint32_t status;
  while (len > 0) {
    // Read the status register.
    status = lsu_read_32(kmac + KMAC_STATUS_REG_OFFSET);

    // Calculate the remaining space in the message FIFO based on the
    // `FIFO_DEPTH` status field.
    size_t free_entries = KMAC_PARAM_NUM_ENTRIES_MSG_FIFO - (
                            (status & KMAC_STATUS_FIFO_DEPTH_MASK) >> KMAC_STATUS_FIFO_DEPTH_INDEX
                          );
    size_t max_len = free_entries * KMAC_PARAM_NUM_BYTES_MSG_FIFO_ENTRY;
    size_t write_len = (len < max_len) ? len : max_len;
    msg_fifo_write(kmac, data, write_len);
    data += write_len;
    len -= write_len;

    // If `processed` is non-null, do not continue after the first iteration;
    // return the number of bytes written and `kDifKmacIncomplete`.
    if (processed != 0) {
      *processed = write_len;
      break;
    }
  }
}

void dif_kmac_squeeze(
    const uintptr_t kmac, dif_kmac_operation_state_t *operation_state,
    uint32_t *out, size_t len, size_t *processed, uint32_t *capacity) {
  if (kmac == 0 || operation_state == 0 || (out == 0 && len != 0)) {
    printf("dif_kmac_squeeze: ERROR arguments may not be NULL.\n");
    while (1);
    return;
  }

  // Set `processed` to 0 so we can return early without setting it again.
  if (processed != 0) {
    *processed = 0;
  }

  // Move into squeezing state (if not already in it).
  // Do this even if the length requested is 0 or too big.
  if (!operation_state->squeezing) {
    if (operation_state->append_d) {
      // The KMAC operation requires that the output length (d) in bits be right
      // encoded and appended to the end of the message.
      // Note: kDifKmacMaxOutputLenWords could be reduced to make this code
      // simpler. For example, a maximum of `(UINT16_MAX - 32) / 32` (just under
      // 8 KiB) would mean that d is guaranteed to be less than 0xFFFF.
      uint32_t d = operation_state->d * 32;
      int len = 1 + (d > 0xFF) + (d > 0xFFFF) + (d > 0xFFFFFF);
      int shift = (len - 1) * 8;
      while (shift >= 8) {
        lsu_write_8(kmac + KMAC_MSG_FIFO_REG_OFFSET,
                           (uint8_t)(d >> shift));
        shift -= 8;
      }
      lsu_write_8(kmac + KMAC_MSG_FIFO_REG_OFFSET, (uint8_t)d);
      lsu_write_8(kmac + KMAC_MSG_FIFO_REG_OFFSET, (uint8_t)len);
    }
    operation_state->squeezing = true;

    // Issue squeeze command.
    lsu_write_32(kmac + KMAC_CMD_REG_OFFSET, KMAC_CMD_CMD_VALUE_PROCESS << KMAC_CMD_CMD_INDEX);
  }

  // If the operation has a fixed length output then the total number of bytes
  // requested must not exceed that length.
  if (operation_state->d != 0 &&
      len > (operation_state->d - operation_state->offset)) {
    printf("dif_kmac_squeeze: ERROR total bytes requested must not exceed fixed output length.\n");
    while (1);
    return;
  }

  if (len == 0) {
    return;
  }

  while (len > 0) {
    size_t n = len;
    size_t remaining = operation_state->r - operation_state->offset;
    if (operation_state->d != 0 && operation_state->d < operation_state->r) {
      remaining = operation_state->d - operation_state->offset;
    }
    if (n > remaining) {
      n = remaining;
    }
    if (n == 0) {
      // Reduce the digest length to reflect consumed output state.
      if (operation_state->d != 0) {
        if (operation_state->d <= operation_state->r) {
          printf("dif_kmac_squeeze: ERROR operation state d less than r.\n");
          while (1);
          return;
        }
        operation_state->d -= operation_state->r;
      }

      // Issue run command to generate more state.
      lsu_write_32(kmac + KMAC_CMD_REG_OFFSET, KMAC_CMD_CMD_VALUE_RUN << KMAC_CMD_CMD_INDEX);
      operation_state->offset = 0;
      continue;
    }

    // Poll the status register until in the 'squeeze' state.
    dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_SQUEEZE_INDEX);

    uint32_t offset =
        KMAC_STATE_REG_OFFSET +
        operation_state->offset * sizeof(uint32_t);
    for (size_t i = 0; i < n; ++i) {
      // Read both shares from state register and combine using XOR.
      uint32_t share0 = lsu_read_32(kmac + offset);
      uint32_t share1 =
          lsu_read_32(kmac + offset + kDifKmacStateShareOffset);
      *out++ = share0 ^ share1;
      offset += sizeof(uint32_t);
    }
    operation_state->offset += n;
    len -= n;
    if (processed != 0) {
      *processed += n;
    }
    // Read also the capacity of the state, if non-NULL buffer is given.
    // This is only useful for testing that capacity is not leaked during
    // sideloaded KMAC operations.
    if (capacity != 0) {
      uint32_t capacity_offset =
          KMAC_STATE_REG_OFFSET +
          operation_state->r * sizeof(uint32_t);
      for (int i = 0; i < kDifKmacStateWords - operation_state->r; ++i) {
        uint32_t share0 = lsu_read_32(kmac + capacity_offset);
        uint32_t share1 = lsu_read_32(
            kmac + capacity_offset + kDifKmacStateShareOffset);
        *capacity++ = share0 ^ share1;
        capacity_offset += sizeof(uint32_t);
      }
    }
  }
}

void dif_kmac_end(
    const uintptr_t kmac, dif_kmac_operation_state_t *operation_state) {
  if (kmac == 0 || operation_state == 0) {
    printf("dif_kmac_end: ERROR arguments may not be NULL.\n");
    while (1);
    return;
  }

  // The hardware should (must?) complete squeeze operation before the DONE
  // command is issued.
  if (!operation_state->squeezing) {
    printf("dif_kmac_end: ERROR hardware must be done squeezing.\n");
    while (1);
    return;
  }
  while (true) {
    uint32_t kmac_status = lsu_read_32(kmac + KMAC_STATUS_REG_OFFSET);
    if (kmac_status & (0x1U << KMAC_STATUS_SHA3_SQUEEZE_INDEX)) {
      break;
    }
  }

  // Issue done command.
  lsu_write_32(kmac + KMAC_CMD_REG_OFFSET, KMAC_CMD_CMD_VALUE_DONE << KMAC_CMD_CMD_INDEX);

  // Reset operation state.
  operation_state->squeezing = false;
  operation_state->append_d = false;
  operation_state->offset = 0;
  operation_state->r = 0;
  operation_state->d = 0;
}
