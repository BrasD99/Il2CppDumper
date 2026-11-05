using System;
using System.Collections.Generic;
using System.IO;

namespace Il2CppDumper
{
    public sealed class WebAssembly : BinaryStream
    {
        private readonly DataSection[] dataSections;
        private readonly uint[] indexedPointerArrays;
        private readonly uint[] stride12Arrays;

        public WebAssembly(Stream stream) : base(stream)
        {
            Is32Bit = true;
            var magic = ReadUInt32();
            var version = ReadInt32();
            if (magic != 0x6D736100)
            {
                throw new InvalidDataException("ERROR: not a WebAssembly binary.");
            }
            _ = version;
            uint[] indexed = Array.Empty<uint>();
            uint[] stride12 = Array.Empty<uint>();
            while (Position < Length)
            {
                var id = ReadULeb128();
                var len = ReadULeb128();
                var end = Position + len;
                if (id == 10)
                {
                    var code = ReadBytes((int)len);
                    indexed = ScanIndexedPointerArrays(code);
                    stride12 = ScanStride12Arrays(code);
                }
                else if (id == 11)
                {
                    dataSections = ReadDataSection(end);
                }
                Position = end;
            }
            if (dataSections == null || dataSections.Length == 0)
            {
                throw new InvalidDataException("ERROR: WebAssembly data section is missing.");
            }
            indexedPointerArrays = indexed;
            stride12Arrays = stride12;
        }

        public WebAssemblyMemory CreateMemory()
        {
            uint bssStart = 0;
            foreach (var dataSection in dataSections)
            {
                var end = dataSection.Offset + (uint)dataSection.Data.Length;
                if (end > bssStart)
                {
                    bssStart = end;
                }
            }
            var capacity = Math.Max(Length, bssStart + 0x1000ul);
            var stream = new MemoryStream(new byte[capacity]);
            foreach (var dataSection in dataSections)
            {
                stream.Position = dataSection.Offset;
                stream.Write(dataSection.Data, 0, dataSection.Data.Length);
            }
            return new WebAssemblyMemory(stream, bssStart, indexedPointerArrays, stride12Arrays);
        }

        private DataSection[] ReadDataSection(ulong sectionEnd)
        {
            var start = Position;
            try
            {
                return ReadDataSegments(sectionEnd, bulkMemory: true);
            }
            catch (InvalidOperationException)
            {
                Position = start;
                return ReadDataSegments(sectionEnd, bulkMemory: false);
            }
        }

        // bulkMemory: flags byte, then optional memidx, then the offset expression.
        // Legacy segments are memidx, then the same expression. Active mem0 segments
        // encoded with flags 0 are identical to the legacy form.
        private DataSection[] ReadDataSegments(ulong sectionEnd, bool bulkMemory)
        {
            var count = ReadULeb128();
            var list = new List<DataSection>();
            for (uint i = 0; i < count; i++)
            {
                if (Position >= sectionEnd)
                {
                    throw new InvalidOperationException("data section ended early");
                }
                var passive = false;
                if (bulkMemory)
                {
                    var flags = ReadByte();
                    if (flags == 1)
                    {
                        passive = true;
                    }
                    else if (flags == 2)
                    {
                        ReadULeb128();
                    }
                    else if (flags != 0)
                    {
                        throw new InvalidOperationException($"unsupported data segment flags {flags}");
                    }
                }
                else
                {
                    ReadULeb128();
                }
                uint offset = 0;
                if (!passive)
                {
                    offset = (uint)ReadInitOffset();
                }
                var size = ReadULeb128();
                if (Position + size > sectionEnd)
                {
                    throw new InvalidOperationException("data segment exceeds section");
                }
                var bytes = ReadBytes((int)size);
                if (!passive)
                {
                    list.Add(new DataSection { Offset = offset, Data = bytes });
                }
            }
            if (Position != sectionEnd)
            {
                throw new InvalidOperationException("data section size mismatch");
            }
            return list.ToArray();
        }

        private int ReadInitOffset()
        {
            var opCode = ReadByte();
            if (opCode != 0x41) // i32.const
            {
                throw new InvalidOperationException();
            }
            var offset = ReadI32Leb();
            if (ReadByte() != 0x0B) // end
            {
                throw new InvalidOperationException();
            }
            if (offset < 0)
            {
                throw new InvalidOperationException("negative data offset");
            }
            return offset;
        }

        private int ReadI32Leb()
        {
            var result = 0;
            var shift = 0;
            byte b;
            do
            {
                b = ReadByte();
                result |= (b & 0x7F) << shift;
                shift += 7;
            } while (b >= 128 && shift < 32);
            if (shift < 32 && (b & 0x40) != 0)
            {
                result |= ~0 << shift;
            }
            return result;
        }

        // Il2CppMethodSpec is 12 bytes, so codegen is i32.const 12 / i32.mul / i32.const <base> / i32.add.
        private static uint[] ScanStride12Arrays(byte[] code)
        {
            var found = new HashSet<uint>();
            for (var i = 0; i + 8 < code.Length; i++)
            {
                if (code[i] != 0x41 || code[i + 1] != 0x0C || code[i + 2] != 0x6C)
                {
                    continue;
                }
                var end = Math.Min(code.Length, i + 3 + 16);
                for (var j = i + 3; j < end; j++)
                {
                    if (code[j] != 0x41)
                    {
                        continue;
                    }
                    if (TryReadSleb(code, j + 1, out var value, out var next)
                        && next < code.Length
                        && code[next] == 0x6A
                        && value > 0x10000
                        && value < 0x10000000)
                    {
                        found.Add((uint)value);
                    }
                    break;
                }
            }
            var result = new uint[found.Count];
            found.CopyTo(result);
            return result;
        }

        // wasm-opt constant-folds loads of il2cpp pointer tables into
        // i32.shl / i32.const <base> / i32.add / i32.load.
        private static uint[] ScanIndexedPointerArrays(byte[] code)
        {
            var found = new HashSet<uint>();
            for (var i = 0; i + 6 < code.Length; i++)
            {
                if (code[i] != 0x74 || code[i + 1] != 0x41)
                {
                    continue;
                }
                if (!TryReadSleb(code, i + 2, out var value, out var next))
                {
                    continue;
                }
                if (next + 1 >= code.Length || code[next] != 0x6A || code[next + 1] != 0x28)
                {
                    continue;
                }
                if (!TryReadUleb(code, next + 2, out _, out var afterAlign))
                {
                    continue;
                }
                if (!TryReadUleb(code, afterAlign, out var offset, out _))
                {
                    continue;
                }
                if (offset != 0 || value <= 0x1000 || value > uint.MaxValue)
                {
                    continue;
                }
                found.Add((uint)value);
            }
            var result = new uint[found.Count];
            found.CopyTo(result);
            return result;
        }

        private static bool TryReadSleb(byte[] code, int offset, out long value, out int next)
        {
            value = 0;
            next = offset;
            var shift = 0;
            byte b = 0;
            while (next < code.Length && shift <= 63)
            {
                b = code[next++];
                value |= (long)(b & 0x7F) << shift;
                shift += 7;
                if (b < 128)
                {
                    if (shift < 64 && (b & 0x40) != 0)
                    {
                        value |= -1L << shift;
                    }
                    return true;
                }
            }
            return false;
        }

        private static bool TryReadUleb(byte[] code, int offset, out ulong value, out int next)
        {
            value = 0;
            next = offset;
            var shift = 0;
            while (next < code.Length && shift <= 63)
            {
                var b = code[next++];
                value |= (ulong)(b & 0x7F) << shift;
                shift += 7;
                if (b < 128)
                {
                    return true;
                }
            }
            return false;
        }
    }
}
