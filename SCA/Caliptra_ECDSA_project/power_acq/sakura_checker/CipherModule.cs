using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;

namespace SAKURA
{
    class CipherModule : IDisposable
    {
        private SBus bus;
        private Stopwatch sw;

        public CipherModule(uint index)
        {
            bus = new SBus(index);
            sw = new Stopwatch();
        }

        public void Dispose()
        {
            bus.Dispose();
        }

        public void Reset()
        {
            bus.SbusWrite((uint)Address.CONT, (uint)Cont.IPRST);
            bus.SbusWrite((uint)Address.CONT, (uint)Cont.ZERO);
        }

        public void SetModeEncrypt(bool encrypt)
        {
            bus.SbusWrite((uint)Address.MODE, (uint)(encrypt ? Mode.ENC : Mode.DEC));
        }

        public void SetKey(byte[] key)
        {
            byte[] fixed_input = new byte[48];
            for (int i = 0; i < 48; i++)
                fixed_input[i] = (byte)0x00;

            bus.SbusWriteBurst((uint)Address.CONST_ZERO, fixed_input, fixed_input.Length);
            fixed_input[3] = (byte)0x01;
            bus.SbusWriteBurst((uint)Address.CONST_ONE, fixed_input, fixed_input.Length);
            fixed_input = new byte[48] { 0xff, 0xff, 0xff, 0xff,
 0xff, 0xff, 0xff, 0xfd,
 0x00, 0x00, 0x00, 0x02,
 0xff, 0xff, 0xff, 0xff,
 0xff, 0xff, 0xff, 0xfb,
 0xff, 0xff, 0xff, 0xfc,
 0xff, 0xff, 0xff, 0xff,
 0xff, 0xff, 0xff, 0xff,
 0xff, 0xff, 0xff, 0xff,
 0xff, 0xff, 0xff, 0xff,
 0xff, 0xff, 0xff, 0xff,
 0xff, 0xff, 0xff, 0xff};
            bus.SbusWriteBurst((uint)Address.CONST_E_a, fixed_input, fixed_input.Length);
            fixed_input = new byte[48] {0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x01,
 0xff, 0xff, 0xff, 0xff,
 0xff, 0xff, 0xff, 0xff,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x01,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00};
            bus.SbusWriteBurst((uint)Address.ONE_MONT, fixed_input, fixed_input.Length);
            fixed_input = new byte[48] {0x4d, 0x3a, 0xad, 0xc2,
 0xfc, 0x86, 0x07, 0x66,
 0x3d, 0xd0, 0x75, 0x65,
 0xee, 0x11, 0x7b, 0xfa,
 0x6e, 0x1e, 0x26, 0xa4,
 0x54, 0x1b, 0x4d, 0x6e,
 0x87, 0x9c, 0x3a, 0xfc,
 0x59, 0xa3, 0x0e, 0xff,
 0x64, 0x54, 0x86, 0x84,
 0x61, 0x4e, 0xde, 0x2b,
 0x81, 0x2f, 0xf7, 0x23,
 0x29, 0x9e, 0x15, 0x13};
            bus.SbusWriteBurst((uint)Address.GX_MONT, fixed_input, fixed_input.Length);
            fixed_input = new byte[48] {0x2b, 0x78, 0xab, 0xc2,
 0x1f, 0x8a, 0xf9, 0x3c,
 0x23, 0x04, 0x3d, 0xad,
 0xa7, 0x2d, 0x55, 0x6e,
 0xcd, 0x38, 0x54, 0x81,
 0x2e, 0x83, 0xb0, 0x50,
 0x8b, 0xad, 0xe7, 0x56,
 0x68, 0xf4, 0xff, 0xd9,
 0xc6, 0xc3, 0x52, 0x19,
 0x39, 0x69, 0xa8, 0x40,
 0xdd, 0x80, 0x02, 0x26,
 0x5a, 0x15, 0xc5, 0xe9};
            bus.SbusWriteBurst((uint)Address.GY_MONT, fixed_input, fixed_input.Length);

            fixed_input = new byte[48] {0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x01,
 0xff, 0xff, 0xff, 0xff,
 0xff, 0xff, 0xff, 0xff,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x01,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00,
 0x00, 0x00, 0x00, 0x00};
            bus.SbusWriteBurst((uint)Address.GZ_MONT, fixed_input, fixed_input.Length);

            
        }

        public void Run(ref byte[] outputtext, byte[] inputtext, int wait, ref double elapsedMillisecond)
        {
            
            bus.SbusWriteBurst((uint)Address.SCALAR, inputtext, inputtext.Length);
            byte[] fixed_input = new byte[2] { 0x01, 0x01 };            
            wait = 50;
            //System.Threading.Thread.Sleep(wait);
            sw.Reset();
            sw.Start();
            bus.SbusWriteBurst((uint)(Address.TRIGGER), fixed_input, fixed_input.Length);
            //System.Threading.Thread.Sleep(wait);
            WaitDone();
            sw.Stop();
            //outputtext = new byte[48];
            bus.SbusReadBurst((uint)Address.Qx_AFFN, fixed_input, fixed_input.Length);
            byte[] tmp1 = new byte[48];
            bus.SbusReadBurst((uint)Address.Qx_AFFN, tmp1, tmp1.Length);
            //---------------------
            bus.SbusReadBurst((uint)Address.Qy_AFFN, fixed_input, fixed_input.Length);
            byte[] tmp2 = new byte[48];
            bus.SbusReadBurst((uint)Address.Qy_AFFN, tmp2, tmp2.Length);
            outputtext = new byte[tmp1.Length + tmp2.Length];
            tmp1.CopyTo(outputtext, 0);
            tmp2.CopyTo(outputtext, tmp1.Length);
            elapsedMillisecond = sw.Elapsed.TotalMilliseconds;
        }

        private void WaitDone()
        {
            uint deneme = (uint)bus.SbusRead((uint)Address.CONT);
            while (deneme == 0x0000)
            {
                deneme = (uint)bus.SbusRead((uint)Address.CONT);
                System.Threading.Thread.Sleep(0);
            }
        }

        private enum Address : ushort
        {
            CONT = 0x0002,
            MODE = 0x000c,
            KEY0 = 0x0100,
            ITEXT0 = 0x0120,
            OTEXT0 = 0x0180,
            TRIGGER    = 0x3000,
            SCALAR     = 0x8000,
            CONST_ZERO = 0x4000,
            CONST_ONE  = 0x4100,
            CONST_E_a  = 0x4200,
            ONE_MONT   = 0x4300,
            GX_MONT    = 0x4400,
            GY_MONT    = 0x4500,
            GZ_MONT    = 0x4600,
            OPR_R0_X   = 0x4800,
            OPR_R0_Y   = 0x4900,
            OPR_R0_Z   = 0x4A00,
            Qx_AFFN    = 0x5000,
            Qy_AFFN    = 0x5100
        }

        private enum Mode : ushort
        {
            ENC = 0x0000,
            DEC = 0x0001
        }

        private enum Cont : ushort
        {
            ZERO = 0x0000,
            RUN = 0x0001,
            KSET = 0x0002,
            IPRST = 0x0004
        }
    }
}