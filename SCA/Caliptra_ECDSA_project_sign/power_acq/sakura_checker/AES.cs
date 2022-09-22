using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Security.Cryptography;

namespace SAKURA
{
    class AES
    {
        private AesCryptoServiceProvider aes;
        private ICryptoTransform enc;
        private ICryptoTransform dec;

        public AES()
        {
            aes = new AesCryptoServiceProvider();
            aes.BlockSize = 128;
            aes.FeedbackSize = 128;
            aes.KeySize = 128;
            aes.Mode = CipherMode.ECB;
            aes.Padding = PaddingMode.None;
            aes.IV = new byte[] { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
        }

        public void SetKey(byte[] key)
        {
            aes.Key = key;
            enc = aes.CreateEncryptor(aes.Key, aes.IV);
            dec = aes.CreateDecryptor(aes.Key, aes.IV);
        }

        public void Encrypt(ref byte[] ciphertext, byte[] key, byte[] plaintext)
        {
            ciphertext = enc.TransformFinalBlock(plaintext, 0, plaintext.Length);
        }

        public void Decrypt(byte[] plaintext, byte[] ciphertext)
        {
            plaintext = dec.TransformFinalBlock(ciphertext, 0, ciphertext.Length);
        }
    }
}