using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace SAKURA_Checker
{
    class TVLA
    {
        private short[] array1;
        private short[] array2;
        private short[] array3;
        private short[] array4;
        private short[] array5;
        private short[] array6;
        private short[] array7;
        private short[] array8;
        private short[] array9;
        private float[] S11;
        private float[] m11;
        private float n11;
        private float[] S12;
        private float[] m12;
        private float n12;
        public float[] t_values;
        //public const int BUFFER_SIZE = 2500; //Number of samples per waveform capture for block captures-masked for 7100 cycles using 2ns sampling interval --change
        public TVLA(int BUFFER_SIZE)
        {
            array1 = new short[12] { 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 };
            array2 = new short[12] { 20, 3, 6, 4, 5, 8, 75, 8, 0, -3, 6, 90 };
            array3 = new short[12] { 53, 7, 5, 49, 5, 8, 75, 8, 110, -3, 6, 9 };
            array4 = new short[12] { 61, 7, 5, 49, 5, 8, 75, 8, 110, -3, 6, 9 };
            array5 = new short[12] { 81, 7, 5, 49, 5, 8, 75, 8, 110, -3, 6, 9 };
            array6 = new short[12] { 5, 7, 5, 49, 5, 8, 75, 8, 110, -3, 6, 9 };
            array7 = new short[12] { 8, 3, 6, 4, 52, 8, 75, 8, 7, -3, 62, 19 };
            array8 = new short[12] { 400, 5, 8, 4, 52, 8, 75, 8, 3, 6, 4, 5 };
            array9 = new short[12] { 6, 3, 6, 4, 5, 8, 75, 8, 0, -3, 6, 90 };
            S11 = new float[BUFFER_SIZE];
            m11 = new float[BUFFER_SIZE];
            n11 = 1;
            S12 = new float[BUFFER_SIZE];
            m12 = new float[BUFFER_SIZE];
            n12 = 1;
            t_values = new float[BUFFER_SIZE];
            initialize_t_vector(ref m11, ref S11, ref n11);
            initialize_t_vector(ref m12, ref S12, ref n12);
        }

        public void initialize_t_vector(ref float[] m, ref float[] S, ref float n)
        {
            for (int i = 0, j = 0; i < m.Length; i++, j++)
            {
                m[i] = (float)1;
                S[i] = (float)0;
            }
            n = (float)1;
        }

        public void array_sub_float(float[] v1, float[] v2, ref float[] r1)
        {
            for (int i = 0, j = 0; i < v2.Length; i++, j++)
            {
                r1[i] = (float)v1[i] - v2[j];
            }
        }

        public void array_subtract(short[] v1, float[] v2, ref float[] r1)
        {
            for (int i = 0, j = 0; i < v2.Length; i++, j++)
            {
                r1[i] = (float)v1[i] - v2[j];
            }
        }

        public void array_const_divison(float[] n1, float d1, ref float[] r1)
        {
            for (int i = 0; i < n1.Length; i++)
            {
                r1[i] = n1[i] / d1;
            }
        }


        public void array_division(float[] v1, float[] v2, ref float[] r1)
        {
            for (int i = 0, j = 0; i < v2.Length; i++, j++)
            {
                r1[i] = v1[i] / v2[j];
            }
        }

        public void array_addition_cum(ref float[] v1, float[] v2)
        {
            for (int i = 0, j = 0; i < v2.Length; i++, j++)
            {
                v1[i] = v1[i] + v2[j];
            }
        }

        public void array_mult(float[] v1, float[] v2, ref float[] r1)
        {
            for (int i = 0, j = 0; i < v2.Length; i++, j++)
            {
                r1[i] = v1[i] * v2[j];
            }
        }

        public void array_sqrt(ref float[] r1)
        {
            for (int i = 0; i < r1.Length; i++)
            {
                r1[i] = (float)Math.Sqrt((double)r1[i]);
            }
        }

        public void running_sdt_mean(short[] x, ref float[] m, ref float[] S, ref float n)
        {
            float[] prev_mean = new float[m.Length];
            Array.Copy(m, prev_mean, m.Length);
            n = n + (float)1;


            //m = m + (x - m) / n
            //(x - m)
            float[] x_minus_m = new float[m.Length];
            array_subtract(x, m, ref x_minus_m);
            //(x - m) / n
            float[] x_minus_m_divide_n = new float[m.Length];
            array_const_divison(x_minus_m, n, ref x_minus_m_divide_n);
            //m = m + (x - m) / n
            array_addition_cum(ref m, x_minus_m_divide_n);

            //S = S + (x - m) * (x - prev_mean)
            array_subtract(x, m, ref x_minus_m);
            //(x - prev_mean)
            float[] x_minus_prev_m = new float[m.Length];
            array_subtract(x, prev_mean, ref x_minus_prev_m);
            //(x - m) * (x - prev_mean)
            float[] x_mult = new float[m.Length];
            array_mult(x_minus_prev_m, x_minus_m, ref x_mult);
            //S = S + (x - m) * (x - prev_mean)
            array_addition_cum(ref S, x_mult);

            //var = S / (n)
            //std = math.sqrt(std)
        }

        public void t_Test(float[] m1, float[] m2, float[] S1, float[] S2, float n1, float n2, ref float[] t_values)
        {
            float[] mean = new float[m1.Length];
            array_sub_float(m1, m2, ref mean);
            float[] S1_tmp = new float[m1.Length];
            array_const_divison(S1, n1, ref S1_tmp);
            array_const_divison(S1_tmp, n1, ref S1_tmp);

            float[] S2_tmp = new float[m1.Length];
            array_const_divison(S2, n2, ref S2_tmp);
            array_const_divison(S2_tmp, n2, ref S2_tmp);
            array_addition_cum(ref S1_tmp, S2_tmp);
            array_sqrt(ref S1_tmp);
            array_division(mean, S1_tmp, ref t_values);

        }

        public void keep_mean_var(short[] x, int group)
        {
            if (group == 1)
                running_sdt_mean(x, ref m11, ref S11, ref n11);
            else
                running_sdt_mean(x, ref m12, ref S12, ref n12);


        }

        public void do_TVLA()
        {

            t_Test(m11, m12, S11, S12, n11, n12, ref t_values);
            //Console.WriteLine("t_values:" + t_values[0]);

        }

        public TVLA ShallowCopy()
        {
            return (TVLA)this.MemberwiseClone();
        }

    }
}
