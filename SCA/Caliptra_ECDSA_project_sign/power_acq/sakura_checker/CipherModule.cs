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
            bus.SbusWriteBurst((uint)Address.KEY0, key, key.Length);
            bus.SbusWrite((uint)Address.CONT, (uint)Cont.KSET);
            //WaitDone();
        }

        public void Run(ref byte[] outputtext, byte[] inputtext, int wait, ref double elapsedMillisecond)
        {
            wait = 50;
            //System.Threading.Thread.Sleep(wait);
            bus.SbusWriteBurst((uint)(Address.ITEXT0), inputtext, inputtext.Length);
            sw.Reset();
            sw.Start();
            bus.SbusWrite((uint)Address.CONT, (uint)Cont.RUN);
            //System.Threading.Thread.Sleep(wait);
            WaitDone();
            sw.Stop();
            outputtext = new byte[48];
            bus.SbusReadBurst((uint)Address.KEY0, outputtext, outputtext.Length);
            bus.SbusReadBurst((uint)Address.ITEXT0, outputtext, outputtext.Length);
            bus.SbusReadBurst((uint)Address.OTEXT0, outputtext, outputtext.Length);
            elapsedMillisecond = sw.Elapsed.TotalMilliseconds;
        }

        private void WaitDone()
        {
            uint deneme = (uint)bus.SbusRead((uint)Address.MODE) ;
            deneme = deneme & 15;
            while (deneme == 0x0004)
            {
                deneme = (uint)bus.SbusRead((uint)Address.MODE) ;
                
            }
            System.Threading.Thread.Sleep(10);
        }

        private enum Address : ushort
        {
            CONT = 0x0002,
            MODE = 0x000c,
            KEY0 = 0x0100,
            ITEXT0 = 0x0200,
            OTEXT0 = 0x0300
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