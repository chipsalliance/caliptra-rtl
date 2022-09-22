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
        int RRNG_off;

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
            int PRNG_off=0;
            byte[] P1_2 = new byte[4];
            byte[] H1_2 = new byte[4];
            byte[] d1 = new byte[2];
            byte[] d2 = new byte[2];
            byte[] P = new byte[2];
            byte[] H = new byte[2];
            byte[] R = new byte[2];
            byte[] K = new byte[2];


            P[0] = inputtext[0]; P[1] = inputtext[1]; H[0] = inputtext[2]; H[1] = inputtext[3];
            R[0] = inputtext[4]; R[1] = inputtext[5]; K[0] = inputtext[6]; K[1] = inputtext[7];
            d1[0] = inputtext[8]; d1[1] = inputtext[9]; d2[0] = inputtext[10]; d2[1] = inputtext[11];
            splitting_two(P, d1, ref P1_2, PRNG_off);
            splitting_two(H, d2, ref H1_2, PRNG_off);

            byte[] plaintext = new byte[12];
            plaintext[0] = P1_2[0]; plaintext[1] = P1_2[1]; plaintext[2] = P1_2[2]; plaintext[3] = P1_2[3];
            plaintext[4] = H1_2[0]; plaintext[5] = H1_2[1]; plaintext[6] = H1_2[2]; plaintext[7] = H1_2[3];
            plaintext[8] = R[0]; plaintext[9] = R[1]; plaintext[10] = K[0]; plaintext[11] = K[1];
            

            wait = 50;
            //System.Threading.Thread.Sleep(wait);
            bus.SbusWriteBurst((uint)(Address.ITEXT0 + 0x0020), plaintext, plaintext.Length);
            sw.Reset();
            sw.Start();
            bus.SbusWrite((uint)Address.CONT, (uint)Cont.RUN);
            //System.Threading.Thread.Sleep(wait);
            WaitDone();
            sw.Stop();
            outputtext = new byte[4];
            bus.SbusReadBurst((uint)Address.OTEXT0, outputtext, outputtext.Length);
            elapsedMillisecond = sw.Elapsed.TotalMilliseconds;
        }

        public void splitting_two(byte[] P, byte[] d, ref byte[] P1, int PRNG_off)
        {
            UInt32 P_int = (((UInt32)P[0])<<8) | ((UInt32)P[1]);
            UInt32 d_int = (((UInt32)d[0])<<8) | ((UInt32)d[1]);

            if (PRNG_off == 1)
                d_int = 8090;

            UInt32 PD = P_int - d_int;
            UInt32 QD = P_int - d_int + 8191;

            UInt32 P1_int;

            if (P_int >= d_int)
                P1_int = PD;
            else
                P1_int = QD;

            P1[1] = (byte)(P1_int & 0xFF);
            P1[0] = (byte)((P1_int>>8) & 0xFF);
            P1[3] = (byte)(d_int & 0xFF);
            P1[2] = (byte)((d_int >> 8) & 0xFF);

        }

        public UInt32 signing(byte[] P)
        {
            UInt32 P_int, H_int, R_int, K_int;
            P_int= H_int= R_int= K_int = 0;
            UInt32 PR, PRH, S;

            for (int i=0; i<P.Length; i=i+2)
            {
                if (i < 2)
                    P_int = (((UInt32)P[i]) << 8) | ((UInt32)P[i + 1]);
                else if (i < 4)
                    H_int = (((UInt32)P[i]) << 8) | ((UInt32)P[i + 1]);
                else if (i < 6)
                    R_int = (((UInt32)P[i]) << 8) | ((UInt32)P[i + 1]);
                else if (i < 8)
                    K_int = (((UInt32)P[i]) << 8) | ((UInt32)P[i + 1]);
            }

            PR = (P_int * R_int);
            PR = PR % 8191;
            PRH = (PR + H_int) % 8191;
            S = (PRH * K_int) % 8191;
            return S;

        }

        public void constraint(ref byte[] P)
        {
            UInt32 P_int;

            for (int i = 0; i < P.Length; i = i+2)
            {
                P_int = (((UInt32)P[i]) << 8) | ((UInt32)P[i + 1]);
                P_int = P_int % 8191;
                P[i + 1] = (byte)(P_int & 0xFF);
                P[i] = (byte)((P_int >> 8) & 0xFF);
            }

        }

        public UInt32 mergeResult(byte[] P)
        {
            UInt32 P1_int, P2_int;
            int i = 0;
            P1_int = (((UInt32)P[i]) << 8) | ((UInt32)P[i + 1]);
            P1_int = P1_int % 8191;
            i = 2;
            P2_int = (((UInt32)P[i]) << 8) | ((UInt32)P[i + 1]);
            P2_int = P2_int % 8191;

            return ((P1_int + P2_int) % 8191);

        }

        private void WaitDone()
        {
            while (bus.SbusRead((uint)Address.CONT) != 0x0000)
            {
                System.Threading.Thread.Sleep(0);
            }
            System.Threading.Thread.Sleep(1);
        }

        private enum Address : ushort
        {
            CONT = 0x0002,
            MODE = 0x000c,
            KEY0 = 0x0100,
            ITEXT0 = 0x0120,
            OTEXT0 = 0x0180
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