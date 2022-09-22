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
            //aes.Key = new byte[1024];
            //aes.Key = key;
            //enc = aes.CreateEncryptor(aes.Key, aes.IV);
            //dec = aes.CreateDecryptor(aes.Key, aes.IV);
        }

        public void Encrypt(ref byte[] ciphertext, byte[] key, byte[] plaintext)
        {
            int i,j;
            int N=1024;
	
            int[] mul_res = new int[N];
            
            int[] c = new int[N];
            int[] r = new int[N];
            int[] act1 = new int[N];
            int[] act2 = new int[N];
            int[] act3 = new int[N];
            int[] act4 = new int[10];
            int bias;

            /*
            string weights_text1 = System.IO.File.ReadAllText(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\weights_mem1.txt");
            string weights_text2 = System.IO.File.ReadAllText(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\weights_mem2.txt");
            string weights_text3 = System.IO.File.ReadAllText(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\weights_mem3.txt");
            string weights_text4 = System.IO.File.ReadAllText(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\weights_mem4.txt");
            string bias_text = System.IO.File.ReadAllText(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\bias_mem1.txt");
            */

            string[] weights_1_lines = System.IO.File.ReadAllLines(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\weights1-to-C.txt");
            string[] weights_2_lines = System.IO.File.ReadAllLines(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\weights2-to-C.txt");
            string[] weights_3_lines = System.IO.File.ReadAllLines(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\weights3-to-C.txt");
            string[] weights_4_lines = System.IO.File.ReadAllLines(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\weights4-to-C.txt");
            string[] bias_lines = System.IO.File.ReadAllLines(@"C:\BinaryConnect\SAKURA-G\BinNet-FPGA\SAKURA_Checker_release_20130902\SAKURA_Checker\bin\Debug\bias_mem.txt");

            for (i = 0; i < 1024; i++)
            {
                for (j = 0; j < 784; j++)
                {
                    act1[i] = act1[i] + ((2*(weights_1_lines[i][j]-48)-1) * plaintext[j]);
                }
                //two's complement bias
                bias=(8 * (bias_lines[i][0] - 48)) + (4 * (bias_lines[i][1] - 48)) + (2 * (bias_lines[i][2] - 48)) + (bias_lines[i][3] - 48);
                if (bias>7)
                    bias=bias-16;

                act1[i] = act1[i] + bias;
                if (act1[i] < 0)
                    act1[i] = -1;
                else
                    act1[i] = 1;
            }

            for (i = 0; i < 1024; i++)
            {
                for (j = 0; j < 1024; j++)
                {
                    act2[i] = act2[i] + (2 * (weights_2_lines[i][j] - 48) - 1) * act1[j];
                }

                bias = (8 * (bias_lines[i+1024][0] - 48)) + (4 * (bias_lines[i+1024][1] - 48)) + (2 * (bias_lines[i+1024][2] - 48)) + (bias_lines[i+1024][3] - 48);
                
                if (bias > 7)
                    bias = bias - 16;
                act2[i] = act2[i] + bias;

                if (act2[i] < 0)
                    act2[i] = -1;
                else
                    act2[i] = 1;
            }

            for (i = 0; i < 1024; i++)
            {
                for (j = 0; j < 1024; j++)
                {
                    act3[i] = act3[i] + (2 * (weights_3_lines[i][j] - 48) - 1) * act2[j];
                }

                bias = (8 * (bias_lines[i + 2048][0] - 48)) + (4 * (bias_lines[i + 2048][1] - 48)) + (2 * (bias_lines[i + 2048][2] - 48)) + (bias_lines[i + 2048][3] - 48);

                if (bias > 7)
                    bias = bias - 16;
                act3[i] = act3[i] + bias;
                
                if (act3[i] < 0)
                    act3[i] = -1;
                else
                    act3[i] = 1;
            }

            int max = 0;
            int ind = 0;
            for (i = 0; i < 10; i++)
            {
                for (j = 0; j < 1024; j++)
                {
                    act4[i] = act4[i] + (2 * (weights_4_lines[i][j] - 48) - 1) * act3[j];
                }

                bias = (8 * (bias_lines[i + 3072][0] - 48)) + (4 * (bias_lines[i + 3072][1] - 48)) + (2 * (bias_lines[i + 3072][2] - 48)) + (bias_lines[i + 3072][3] - 48);

                if (bias > 7)
                    bias = bias - 16;
                act4[i] = act4[i] + bias;
                if (Math.Abs(act4[i]) > max)
                {
                    max = Math.Abs(act4[i]);
                    ind = i;
                }
            }
            byte[] temp = new byte[3];
            temp[0] = Convert.ToByte(max>>8);
            temp[1] = Convert.ToByte(max%256);
            temp[2] = Convert.ToByte(ind);


            ciphertext = temp;
                    
        }

        public void Decrypt(byte[] plaintext, byte[] ciphertext)
        {
            plaintext = dec.TransformFinalBlock(ciphertext, 0, ciphertext.Length);
        }
    }
}
