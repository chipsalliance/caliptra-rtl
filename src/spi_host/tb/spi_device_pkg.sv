// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

package spi_device_pkg;

  typedef logic [7:0] spi_byte_t;

  typedef enum spi_byte_t {
    CmdNone = 8'h 00,

    CmdWriteStatus1 = 8'h 01,
    CmdWriteStatus2 = 8'h 31,
    CmdWriteStatus3 = 8'h 11,

    CmdReadStatus1 = 8'h 05,
    CmdReadStatus2 = 8'h 35,
    CmdReadStatus3 = 8'h 15,

    CmdJedecId = 8'h 9F,

    CmdPageProgram     = 8'h 02,
    CmdQuadPageProgram = 8'h 32, // Not supported

    CmdSectorErase  = 8'h 20, // 4kB erase
    CmdBlockErase32 = 8'h 52, // 32kB
    CmdBlockErase64 = 8'h D8, // 64kB

    CmdReadData   = 8'h 03,
    CmdReadFast   = 8'h 0B, // with Dummy
    CmdReadDual   = 8'h 3B,
    CmdReadQuad   = 8'h 6B,
    CmdReadDualIO = 8'h BB,
    CmdReadQuadIO = 8'h EB,

    CmdWriteDisable = 8'h 04,
    CmdWriteEnable  = 8'h 06,

    CmdEn4B = 8'h B7,
    CmdEx4B = 8'h E9,

    CmdReadSfdp = 8'h 5A,

    CmdChipErase = 8'h C7,

    CmdEnableReset = 8'h 66,
    CmdResetDevice = 8'h 99
  } spi_cmd_e;

endpackage : spi_device_pkg
