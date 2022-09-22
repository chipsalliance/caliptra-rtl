using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using FTD2XX_NET;

namespace SAKURA
{
    interface RawInterface
    {
        void open();
        void close();
        void read(byte[] buf, int len);
        void write(byte[] buf, int len);
    }

    class FT245 : RawInterface
    {
        const uint ReadTimeoutMilliseconds = 100;
        const uint WriteTimeoutMilliseconds = 100;
        const byte LatencyMilliseconds = 2;  // available from 2ms to 255ms

        private FTDI ftdi = new FTDI();
        uint index;

        public FT245(uint index)
        {
            this.index = index;
        }

        public void open()
        {
            FTDI.FT_STATUS st;
            /*
            uint devcount = 0;
            ftdi.GetNumberOfDevices(ref devcount);
            if (devcount == 0)
            {
                throw new SystemException("Device not found");
            }
             */
            st = ftdi.OpenByIndex(index);

            if (st != FTDI.FT_STATUS.FT_OK)
            {
                throw new SystemException(string.Format("Failed to open device {0}. ({1})", index, st.ToString()));
            }
            
            ftdi.ResetDevice();
            ftdi.Purge(FTDI.FT_PURGE.FT_PURGE_RX | FTDI.FT_PURGE.FT_PURGE_TX);
            ftdi.SetTimeouts(ReadTimeoutMilliseconds, WriteTimeoutMilliseconds);
            ftdi.SetLatency(LatencyMilliseconds);
        }

        public void close()
        {
            ftdi.Close();
        }

        public void read(byte[] buf, int len)
        {
            uint rlen = 0;
            ftdi.Read(buf, (uint)len, ref rlen);
        }

        public void write(byte[] buf, int len)
        {
            uint wlen = 0;
            ftdi.Write(buf, (uint)len, ref wlen);
        }  
    }
}
