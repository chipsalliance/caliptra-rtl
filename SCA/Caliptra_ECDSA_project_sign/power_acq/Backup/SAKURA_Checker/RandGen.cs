using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace SAKURA
{
    public class RandGen
    {
        private int seedKey;
        private int seedPlaintext;
        private Random randKey;
        private Random randPlaintext;

        public RandGen(int seedKey, int seedPlaintext)
        {
            this.seedKey = seedKey;
            this.seedPlaintext = seedPlaintext;
            randKey = new Random(seedKey);
            randPlaintext = new Random(seedPlaintext);
        }

        public void restartKeyPrng()
        {
            randKey = new Random(seedKey);
        }

        public void restartPlaintextPrng()
        {
            randPlaintext = new Random(seedPlaintext);
        }

        public byte[] generatePlaintext()
        {
            byte[] plaintext = new byte[784];
            //randPlaintext = new Random();
            for (int i = 0; i < 784; i++)
            {
                plaintext[i] = (byte)randPlaintext.Next(256);
            }
            return plaintext;
        }

        public byte[] generateKey(bool generate56bit)
        {
            byte[] key = new byte[1024];
            byte n1,n2,n3,n4;
            UInt32 n;
            for (int i = 0; i < 1024; i++)
            {
                n1 = (byte)randKey.Next(256);
                n2 = (byte)randKey.Next(256);
                n3 = (byte)randKey.Next(256);
                n4 = (byte)randKey.Next(256);
                n = Convert.ToUInt32(Convert.ToUInt32(n1) * Convert.ToUInt32(16777216) + n2 * 65536 + n3 * 256 + n4);
                n = ((n & 0xAAAAAAAA) >> 1) + (n & 0x55555555);
                n = ((n & 0xCCCCCCCC) >> 2) + (n & 0x33333333);
                n = ((n & 0xF0F0F0F0) >> 4) + (n & 0x0F0F0F0F);
                n = ((n & 0xFF00FF00) >> 8) + (n & 0x00FF00FF);
                n = ((n & 0xFFFF0000) >> 16) + (n & 0x0000FFFF);
                if (n == 32)
                    n = n-33;
                else if (n >= 16)
                    n = n - 16;
                else if (n < 16)
                    n = n + 16;
                key[i] = Convert.ToByte(n);
                if (generate56bit && i <= 8)
                {
                    key[i] = (byte)i;
                }
            }
            return key;
        }
    }
}
