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
            byte[] plaintext = new byte[16];
            for (int i = 0; i < 16; i++)
            {
                plaintext[i] = (byte)randPlaintext.Next(256);
            }
            return plaintext;
        }

        public int generateRndOrder()
        {
            int plaintext;
            plaintext = (randPlaintext.Next(2))&1;
            return plaintext;
        }

        public byte[] generateKey(bool generate56bit)
        {
            byte[] key = new byte[16];
            for (int i = 0; i < 16; i++)
            {
                key[i] = (byte)randKey.Next(256);
                if (generate56bit && i <= 8)
                {
                    key[i] = (byte)i;
                }
            }
            return key;
        }
    }
}