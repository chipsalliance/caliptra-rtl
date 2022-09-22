/**************************************************************************
 *
 *     ooooooooo.    o8o                       
 *     `888   `Y88.  `''                       
 *      888   .d88' oooo   .ooooo.   .ooooo.   
 *      888ooo88P'  `888  d88' `'Y8 d88' `88b  
 *      888          888  888       888   888  
 *      888          888  888   .o8 888   888  
 *     o888o        o888o `Y8bod8P' `Y8bod8P'  
 *
 *
 *    Copyright Pico Technology Ltd 1995-2015
 *
 * 
 *    For sales and general information visit
 *    https://www.picotech.com   https://www.picoauto.com
 *    
 *    For help and support visit
 *    https://www.picotech.com/tech-support
 * 
 *    If you have what it takes to join us visit
 *    http://pico.jobs/
 *
 *
 **************************************************************************/

using System;
using System.Runtime.InteropServices;

namespace SAKURA
{
    public class PinnedArray<T> : IDisposable
    {
        GCHandle _pinnedHandle;
        private bool _disposed;

        public PinnedArray(int arraySize) : this(new T[arraySize]) { }

        public PinnedArray(T[] array)
        {
            _pinnedHandle = GCHandle.Alloc(array, GCHandleType.Pinned);
        }

        ~PinnedArray()
        {
            Dispose(false);
        }

        public T[] Target
        {
            get { return (T[])_pinnedHandle.Target; }
        }

        public static implicit operator T[](PinnedArray<T> a)
        {
            if (a == null)
                return null;

            return (T[])a._pinnedHandle.Target;
        }

        public void Dispose()
        {
            Dispose(true);
            GC.SuppressFinalize(this);
        }

        private void Dispose(bool disposing)
        {
            if (_disposed)
                return;

            _disposed = true;

            if (disposing)
            {
                // Dispose of any IDisposable members
            }

            _pinnedHandle.Free();
        }
    }
}
