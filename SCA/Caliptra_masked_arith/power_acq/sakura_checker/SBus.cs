using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace SAKURA
{
    class SBus : IDisposable
    {
        private RawInterface rif;
        private const int MAX_BUF = 8192;
        private byte[] wbuf = new byte[MAX_BUF];
        private byte[] rbuf = new byte[MAX_BUF];

        public SBus(uint index)
        {
            this.rif = new FT245(index);
            this.rif.open();
        }

        public void Dispose()
        {
            this.rif.close();
        }

        public uint SbusRead(uint addr)
        {
            wbuf[0] = 0x00;
            wbuf[1] = (byte)((addr >> 8) & 0xff);
            wbuf[2] = (byte)(addr & 0xff);
            rif.write(wbuf, 3);
            rif.read(rbuf, 2);
            return (uint)(rbuf[0] << 8 | rbuf[1]);
        }

        public void SbusReadBurst(uint addr, byte[] data, int len)
        {
            for (int i = 0; i < MAX_BUF; i++)
            {
                wbuf[i] = 0;
            }
            for (int i = 0; i < len / 2; i++)
            {
                wbuf[i * 3 + 0] = 0x00;
                wbuf[i * 3 + 1] = (byte)(((addr + i * 2) >> 8) & 0xff);
                wbuf[i * 3 + 2] = (byte)((addr + i * 2) & 0xff);
            }
            //System.Threading.Thread.Sleep(500); 
            rif.write(wbuf, 3 * (len / 2));
            rif.read(data, len);
        }

        public void SbusWrite(uint addr, uint data)
        {
            wbuf[0] = 0x01;
            wbuf[1] = (byte)((addr >> 8) & 0xff);
            wbuf[2] = (byte)(addr & 0xff);
            wbuf[3] = (byte)((data >> 8) & 0xff);
            wbuf[4] = (byte)(data & 0xff);
            rif.write(wbuf, 5);
        }

        public void SbusWriteBurst(uint addr, byte[] data, int len)
        {
            for (int i = 0; i < MAX_BUF; i++)
            {
                wbuf[i] = 0;
            }

            for (int i = 0; i < len / 2; i++)
            {
                wbuf[i * 5 + 0] = 0x01;
                wbuf[i * 5 + 1] = (byte)(((addr + i * 2) >> 8) & 0xff);
                wbuf[i * 5 + 2] = (byte)((addr + i * 2) & 0xff);
                wbuf[i * 5 + 3] = data[i * 2];
                wbuf[i * 5 + 4] = data[i * 2 + 1];
            }
            rif.write(wbuf, 5 * (len / 2));
        }
    }
}