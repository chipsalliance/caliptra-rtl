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

        public void SetKey(byte[] key, bool enablemask)
        {
            int i;
            byte[] key_rev = new byte[2048];
            for (i = 0; i < 1024; i++)
            {
                key_rev[2047-i*2] = key[i];
            }
            //key_rev[1] = 1;
            
            bus.SbusWriteBurst((uint)Address.KEY0, key_rev, key_rev.Length);
            bus.SbusWrite((uint)Address.CONT, (uint)Cont.KSET);
            WaitDone();
        }

        public void Run(ref byte[] HWOut, ref byte[] HWMask, byte[] inputtext, int wait, ref double elapsedMillisecond)
        {
            int i;
            byte[] inputtext_rev = new byte[784*2];
            for (i = 0; i < 784; i++)
            {
                inputtext_rev[(i * 2)+1] = inputtext[i];
            }

            bus.SbusWriteBurst((uint)(Address.ITEXT0), inputtext_rev, inputtext.Length*2);
            sw.Reset();
            sw.Start();
            bus.SbusWrite((uint)Address.CONT, (uint)Cont.RUN);
            System.Threading.Thread.Sleep(wait);
            WaitDone();
            sw.Stop();
            byte[] outputtext = new byte[4];
            bus.SbusReadBurst((uint)Address.OTEXT0, outputtext, outputtext.Length);
            elapsedMillisecond = sw.Elapsed.TotalMilliseconds;
            HWOut = new byte[3];
            HWOut[0] = outputtext[0];
            HWOut[1] = outputtext[1];
            HWOut[2] = outputtext[3];
            /*
            HWOut = new byte[2048];
            HWMask = new byte[32];
            int j;
            for (j = 0; j < 2048; j++)
            {
                //HWOut[i] = Convert.ToByte(outputtext[i] ^ outputtext[i + 32]);
                //HWMask[i] = outputtext[i];
                HWOut[j] = outputtext[j];
            }
            */
        }

        private void WaitDone()
        {
            while (bus.SbusRead((uint)Address.CONT) != 0x0000)
            {
                System.Threading.Thread.Sleep(0);
            }
        }

        private enum Address : ushort
        {
            CONT = 0x0002,
            MODE = 0x000c,
            KEY0 = 0x0100,
            ITEXT0 = 0x0900,
            OTEXT0 = 0x1100
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
