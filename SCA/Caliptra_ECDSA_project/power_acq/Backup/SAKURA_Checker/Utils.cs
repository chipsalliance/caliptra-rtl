using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

namespace SAKURA
{
    class Utils
    {
        public static string formHexlString(string str)
        {
            Regex reg = new Regex("(^ +)|( +$)");
            string strTrim = reg.Replace(str, "");
            string[] strSplit = Regex.Split(strTrim, " +");
            return String.Join(" ", strSplit);
        }

        public static string byteArrayToString(byte[] data)
        {
            if (data == null)
            {
                return "";
            }

            string str = "";
            if (data.Length > 0)
            {
                for (int i = 0; i < data.Length - 1; i++)
                {
                    str += string.Format("{0:X2} ", data[i]);
                }
                str += string.Format("{0:X2}", data[data.Length - 1]);
            }
            return str;
        }

        public static byte[] stringToByteArray(string hexString)
        {
            string[] strSplit = hexString.Split(' ');
            if (strSplit[0] == "")
            {
                return new byte[0];
            }
            var bytesList = new List<byte>();
            foreach (string hex in strSplit)
            {
                bytesList.Add((byte)Convert.ToByte(hex, 16));
            }
            return bytesList.ToArray();
        }

        public static bool differenceByteArray(ref byte[] difference, byte[] input1, byte[] input2)
        {
            bool diff = false;
            difference = new byte[3];

            for (int i = 0; i < difference.Length; i++)
            {
                difference[i] = (byte)(input1[i] ^ input2[i]);
                if (difference[i] != 0)
                {
                    diff = true;
                }
            }
            return diff;
        }
    }
}
