// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Taken from KMAC device interface function in OpenTitan:
// https://github.com/lowRISC/opentitan/blob/master/sw/device/lib/dif/dif_kmac.h

#ifndef SHA3_KMAC_HEADER
#define SHA3_KMAC_HEADER

#include "caliptra_defines.h"
#include "riscv_hw_if.h"
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

// Parameter definitions.
#define KMAC_PARAM_NUM_ENTRIES_MSG_FIFO (10)
#define KMAC_PARAM_NUM_BYTES_MSG_FIFO_ENTRY (8)

// Shadowed config regsiter definitions.
#define KMAC_CFG_SHADOWED_REG_OFFSET (0x14)
#define KMAC_CFG_SHADOWED_KSTRENGTH_INDEX (1)
#define KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128 (0x0)
#define KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224 (0x1)
#define KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256 (0x2)
#define KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L384 (0x3)
#define KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L512 (0x4)
#define KMAC_CFG_SHADOWED_MODE_INDEX (4)
#define KMAC_CFG_SHADOWED_MODE_VALUE_SHA3   (0x0)
#define KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE  (0x2)
#define KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE (0x3)

// Command register definitions.
#define KMAC_CMD_REG_OFFSET (0x18)
#define KMAC_CMD_CMD_INDEX (0)
#define KMAC_CMD_CMD_VALUE_START   (0x1d)
#define KMAC_CMD_CMD_VALUE_PROCESS (0x2e)
#define KMAC_CMD_CMD_VALUE_RUN     (0x31)
#define KMAC_CMD_CMD_VALUE_DONE    (0x16)

// Status register definitions.
#define KMAC_STATUS_REG_OFFSET (0x1c)
#define KMAC_STATUS_SHA3_IDLE_INDEX    (0)
#define KMAC_STATUS_SHA3_ABSORB_INDEX  (1)
#define KMAC_STATUS_SHA3_SQUEEZE_INDEX (2)
#define KMAC_STATUS_FIFO_DEPTH_INDEX   (8)
#define KMAC_STATUS_FIFO_DEPTH_MASK    (0x1F00)

// Keccak state memory register definitions.
#define KMAC_STATE_REG_OFFSET (0x400)

// Message FIFO register definitions.
#define KMAC_MSG_FIFO_REG_OFFSET (0x800)

/**
 * Maximum lengths supported by the KMAC unit.
 */
enum {

  /**
   * The maximum length in bytes of a customization string (S) before it has
   * been encoded.
   */
  kDifKmacMaxCustomizationStringLen = 32,

  /**
   * The maximum number of bytes required to encode the length of the
   * customization string.
   *
   * Assumes maximum customization string length of 32 bytes (256 bits).
   */
  kDifKmacMaxCustomizationStringOverhead = 3,

  /**
   * The maximum length in bytes of a function name (N) before it has been
   * encoded.
   */
  kDifKmacMaxFunctionNameLen = 4,

  /**
   * The maximum number of bytes required to encode the length of the function
   * name.
   *
   * Assumes maximum function name length of 4 bytes (32 bits).
   */
  kDifKmacMaxFunctionNameOverhead = 2,

  /**
   * The maximum output length (L) that can be set when starting a KMAC
   * operation.
   *
   * The length is in 32-bit words and is designed to be low enough that the
   * length in bits can still be represented by an unsigned 32-bit integer.
   */
  kDifKmacMaxOutputLenWords = (UINT32_MAX - 32) / 32,

  /**
   * The maximum key length supported by the KMAC operation.
   *
   * The length is in 32-bit words.
   */
  kDifKmacMaxKeyLenWords = 512 / 32,

  /**
   * The length of the software entropy seed.
   *
   * The length is in 32-bit words.
   */
  kDifKmacEntropySeedWords = 6,
  /**
   * The offset of the second share within the output state register.
   */
  kDifKmacStateShareOffset = 0x100,
  /**
   * The size of the Keccak state in words (i.e. 1600 bits).
   */
  kDifKmacStateWords = 1600 / 8 / sizeof(uint32_t),
};

/**
 * Supported SHA-3 modes of operation.
 */
typedef enum dif_kmac_mode_sha3 {
  /** SHA-3 with 224 bit strength. */
  kDifKmacModeSha3Len224,
  /** SHA-3 with 256 bit strength. */
  kDifKmacModeSha3Len256,
  /** SHA-3 with 384 bit strength. */
  kDifKmacModeSha3Len384,
  /** SHA-3 with 512 bit strength. */
  kDifKmacModeSha3Len512,
} dif_kmac_mode_sha3_t;

/**
 * Digest lengths in 32-bit words.
 */
#define DIGEST_LEN_SHA3_224 (224 / 32)
#define DIGEST_LEN_SHA3_256 (256 / 32)
#define DIGEST_LEN_SHA3_384 (384 / 32)
#define DIGEST_LEN_SHA3_512 (512 / 32)
#define DIGEST_LEN_SHA3_MAX DIGEST_LEN_SHA3_512

/**
 * Supported SHAKE modes of operation.
 */
typedef enum dif_kmac_mode_shake {
  /** SHAKE with 128 bit strength. */
  kDifKmacModeShakeLen128,
  /** SHAKE with 256 bit strength. */
  kDifKmacModeShakeLen256,
} dif_kmac_mode_shake_t;

#define DIGEST_LEN_SHAKE_MAX 102

/**
 * A KMAC operation state context.
 */
typedef struct dif_kmac_operation_state {
  /**
   * Whether the 'squeezing' phase has been started.
   */
  bool squeezing;

  /**
   * Flag indicating whether the output length (d) should be right encoded in
   * software and appended to the end of the message. The output length is
   * required to be appended to the message as part of a KMAC operation.
   */
  bool append_d;

  /**
   * Offset into the output state.
   */
  size_t offset;

  /**
   * The rate (r) in 32-bit words.
   */
  size_t r;

  /**
   * The output length (d) in 32-bit words.
   *
   * If the output length is not fixed then this field will be set to 0.
   *
   * Note: if the output length is fixed length will be modified to ensure that
   * `d - offset` always accurately reflects the number of words remaining.
   */
  size_t d;
} dif_kmac_operation_state_t;

/**
 * Poll until a given flag in the status register is set.
 *
 * @param kmac A KMAC handle.
 * @param flag the
 * @return The result of the operation.
 */
void dif_kmac_poll_status(const uintptr_t kmac, uint32_t flag);

/**
 * Start a SHA-3 operation.
 *
 * SHA-3 operations have a fixed output length.
 *
 * See NIST FIPS 202 [1] for more information about SHA-3.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param mode The SHA-3 mode of operation.
 * @return The result of the operation.
 */
void dif_kmac_mode_sha3_start(
    const uintptr_t kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_sha3_t mode);

/**
 * Start a SHAKE operation.
 *
 * SHAKE operations have a variable (XOF) output length.
 *
 * See NIST FIPS 202 [1] for more information about SHAKE.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param mode The mode of operation.
 * @return The result of the operation.
 */
void dif_kmac_mode_shake_start(
    const uintptr_t kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_shake_t mode);

/**
 * Absorb bytes from the message provided.
 *
 * If `processed` is non-NULL, then this function will write the remaining
 * space in the FIFO and update `processed` with the number of bytes written.
 * The caller should adjust the `msg` pointer and `len` parameters and call
 * again as needed until all input has been written.
 *
 * If `processed` is NULL, then this function will block until the entire
 * message has been processed or an error occurs.
 *
 * If big-endian mode is enabled for messages (`message_big_endian`) only the
 * part of the message aligned to 32-bit word boundaries will be byte swapped.
 * Unaligned leading and trailing bytes will be written into the message as-is.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param msg Pointer to data to absorb.
 * @param len Number of bytes of data to absorb.
 * @param[out] processed Number of bytes processed (optional).
 * @preturn The result of the operation.
 */
void dif_kmac_absorb(
    const uintptr_t kmac, dif_kmac_operation_state_t *operation_state,
    const void *msg, size_t len, size_t *processed);


/**
 * Squeeze bytes into the output buffer provided.
 *
 * Requesting a squeeze operation will prevent any further absorption operations
 * from taking place.
 *
 * If `kDifKmacIncomplete` is returned then the hardware is currently
 * recomputing the state and the output was only partially written. The output
 * pointer and length should be updated according to the number of bytes
 * processed and the squeeze operation continued at a later time.
 *
 * If `processed` is not provided then this function will block until `len`
 * bytes have been written to `out` or an error occurs.
 *
 * Normally, the capacity part of Keccak state is and should not be read
 * as part of a regular cryptographic operation. However, this function
 * can also read the capacity for testing purposes.
 * When `capacity` is a non-NULL pointer, at the end of the operation, the
 * capacity part of the Keccak state is also read and written into this buffer.
 * The capacity is read for each output round, meaning that if the requested
 * digest is larger than a single Keccak round can provide (i.e. the rate), then
 * the additional rounds also update this buffer. Hence it should be large
 * enough to accommodate `ceil(digest_len/rate_len) * capacity_len`.
 * `capacity` can be set to NULL to skip reading the capacity.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param[out] out Pointer to output buffer.
 * @param[out] len Number of 32-bit words to write to output buffer.
 * @param[out] processed Number of 32-bit words written to output buffer
 * (optional).
 * @param[out] capacity Optional buffer to read capacity along with the digest.
 * @preturn The result of the operation.
 */
void dif_kmac_squeeze(
    const uintptr_t kmac, dif_kmac_operation_state_t *operation_state,
    uint32_t *out, size_t len, size_t *processed, uint32_t *capacity);

/**
 * Ends a squeeze operation and resets the hardware so it is ready for a new
 * operation.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @return The result of the operation.
 */
void dif_kmac_end(
    const uintptr_t kmac, dif_kmac_operation_state_t *operation_state);

#endif // SHA3_KMAC_HEADER
