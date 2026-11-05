using System;
using System.IO;

namespace Il2CppDumper
{
    public sealed class WebAssemblyMemory : Il2Cpp
    {
        private readonly uint bssStart;
        private readonly uint[] indexedPointerArrays;
        private readonly uint[] stride12Arrays;
        private int[] typeFieldCounts;

        // Read at realStart+8, this value is genericMethodPointersCount and must exceed
        // AutoPlusInit's wasm limit so version 31 is kept and the address shifts back by 8.
        private const uint Version31RealignmentMarker = 0x40000;

        public WebAssemblyMemory(Stream stream, uint bssStart, uint[] indexedPointerArrays, uint[] stride12Arrays) : base(stream)
        {
            Is32Bit = true;
            this.bssStart = bssStart;
            this.indexedPointerArrays = indexedPointerArrays ?? Array.Empty<uint>();
            this.stride12Arrays = stride12Arrays ?? Array.Empty<uint>();
        }

        public void SetTypeFieldCounts(int[] counts)
        {
            typeFieldCounts = counts;
        }

        public override ulong MapVATR(ulong addr)
        {
            return addr;
        }

        public override ulong MapRTVA(ulong addr)
        {
            return addr;
        }

        public override bool PlusSearch(int methodCount, int typeDefinitionsCount, int imageCount)
        {
            var sectionHelper = GetSectionHelper(methodCount, typeDefinitionsCount, imageCount);
            var codeRegistration = sectionHelper.FindCodeRegistration();
            var metadataRegistration = sectionHelper.FindMetadataRegistration();
            if (codeRegistration == 0 || metadataRegistration == 0)
            {
                if (TryReconstructRegistrations(methodCount, typeDefinitionsCount, imageCount, out var code, out var meta))
                {
                    Console.WriteLine("WebAssembly registrations are inlined as i32.const; reconstructed them.");
                    codeRegistration = code;
                    metadataRegistration = meta;
                }
            }
            return AutoPlusInit(codeRegistration, metadataRegistration);
        }

        public override bool Search()
        {
            return false;
        }

        public override bool SymbolSearch()
        {
            return false;
        }

        public override SectionHelper GetSectionHelper(int methodCount, int typeDefinitionsCount, int imageCount)
        {
            var dataEnd = bssStart > 1024 ? bssStart : Length;
            var exec = new SearchSection
            {
                offset = 0,
                offsetEnd = (ulong)methodCount, //hack
                address = 0,
                addressEnd = (ulong)methodCount //hack
            };
            var data = new SearchSection
            {
                offset = 1024,
                offsetEnd = dataEnd,
                address = 1024,
                addressEnd = dataEnd
            };
            var bss = new SearchSection
            {
                offset = bssStart,
                offsetEnd = Length,
                address = bssStart,
                addressEnd = Length
            };
            var sectionHelper = new SectionHelper(this, methodCount, typeDefinitionsCount, metadataUsagesCount, imageCount);
            sectionHelper.SetSection(SearchSectionType.Exec, exec);
            sectionHelper.SetSection(SearchSectionType.Data, data);
            sectionHelper.SetSection(SearchSectionType.Bss, bss);
            return sectionHelper;
        }

        public override bool CheckDump() => false;

        private bool TryReconstructRegistrations(int methodCount, int typeDefinitionsCount, int imageCount, out ulong codeRegistration, out ulong metadataRegistration)
        {
            codeRegistration = 0;
            metadataRegistration = 0;
            var imageSize = (int)Math.Min(bssStart, Length);
            if (imageSize < 0x1000 || typeDefinitionsCount <= 0 || imageCount <= 0)
            {
                return false;
            }
            Position = 0;
            var image = ReadBytes(imageSize);

            var modules = FindCodeGenModules(image, imageCount);
            var types = FindTypesArray(image);
            var fieldOffsets = FindFieldOffsets(image, typeDefinitionsCount, types);
            if (modules == 0 || types == 0 || fieldOffsets == 0)
            {
                Console.WriteLine($"WebAssembly reconstruct failed: modules={modules:x} types={types:x} fieldOffsets={fieldOffsets:x}");
                return false;
            }
            var typesCount = CountTypeRun(image, types);
            var methodSpecs = 0u;
            var methodSpecsCount = 0;
            var genericInsts = 0u;
            var genericInstsCount = 0;
            if (TryFindMethodSpecs(image, methodCount, fieldOffsets, out methodSpecs, out methodSpecsCount, out var maxInstIndex))
            {
                genericInsts = FindGenericInsts(image, maxInstIndex + 1);
                if (genericInsts != 0)
                {
                    genericInstsCount = CountGenericInsts(image, genericInsts);
                }
                else
                {
                    methodSpecs = 0;
                    methodSpecsCount = 0;
                }
            }
            Console.WriteLine($"codeGenModules: {modules:x} ({imageCount})");
            Console.WriteLine($"types: {types:x} ({typesCount})");
            Console.WriteLine($"fieldOffsets: {fieldOffsets:x} ({typeDefinitionsCount})");
            Console.WriteLine($"methodSpecs: {methodSpecs:x} ({methodSpecsCount})");
            Console.WriteLine($"genericInsts: {genericInsts:x} ({genericInstsCount})");
            if (typesCount < typeDefinitionsCount)
            {
                return false;
            }

            var scratch = (bssStart + 15u) & ~15u;
            if (scratch + 256 > Length)
            {
                return false;
            }
            WriteCodeRegistration(scratch, (uint)imageCount, modules);
            var meta = scratch + 128;
            WriteMetadataRegistration(meta, (uint)typesCount, types, (uint)typeDefinitionsCount, fieldOffsets, (uint)genericInstsCount, genericInsts, (uint)methodSpecsCount, methodSpecs);
            // AutoPlusInit reads version 31 at this address, sees the realignment marker, and steps back 8 bytes.
            codeRegistration = scratch + 8;
            metadataRegistration = meta;
            return true;
        }

        private uint FindCodeGenModules(byte[] image, int imageCount)
        {
            foreach (var baseAddr in indexedPointerArrays)
            {
                if (CountModules(image, baseAddr, imageCount) >= imageCount * 9 / 10)
                {
                    return baseAddr;
                }
            }
            var feature = new byte[] { 0x6D, 0x73, 0x63, 0x6F, 0x72, 0x6C, 0x69, 0x62, 0x2E, 0x64, 0x6C, 0x6C, 0x00 };
            foreach (var index in image.Search(feature))
            {
                foreach (var nameSlot in FindPointers(image, (uint)index))
                {
                    if (!IsCodeGenModule(image, nameSlot))
                    {
                        continue;
                    }
                    foreach (var slot in FindPointers(image, nameSlot))
                    {
                        var runStart = slot;
                        var runCount = 1;
                        while (runStart >= 4 && IsCodeGenModule(image, ReadU32(image, (int)runStart - 4)))
                        {
                            runStart -= 4;
                            runCount++;
                        }
                        var forward = slot + 4;
                        while (forward + 4 <= (uint)image.Length && IsCodeGenModule(image, ReadU32(image, (int)forward)))
                        {
                            forward += 4;
                            runCount++;
                        }
                        if (runCount == imageCount)
                        {
                            return runStart;
                        }
                    }
                }
            }
            return 0;
        }

        private uint FindTypesArray(byte[] image)
        {
            uint best = 0;
            var bestRun = 0;
            foreach (var addr in indexedPointerArrays)
            {
                var run = CountTypeRun(image, addr);
                if (run > bestRun)
                {
                    bestRun = run;
                    best = addr;
                }
            }
            return bestRun > 1000 ? best : 0;
        }

        private uint FindFieldOffsets(byte[] image, int typeDefinitionsCount, uint types)
        {
            var counts = typeFieldCounts != null && typeFieldCounts.Length == typeDefinitionsCount ? typeFieldCounts : null;
            uint best = 0;
            var bestScore = 0;
            foreach (var addr in indexedPointerArrays)
            {
                if (addr == types)
                {
                    continue;
                }
                var score = counts != null
                    ? ScoreFieldOffsetsByCounts(image, addr, counts)
                    : ScoreFieldOffsets(image, addr, typeDefinitionsCount);
                if (score > bestScore || (score == bestScore && score > 0 && addr < best))
                {
                    bestScore = score;
                    best = addr;
                }
            }
            if (counts != null)
            {
                return bestScore * 10 >= typeDefinitionsCount * 9 ? best : 0;
            }
            return bestScore > Math.Max(500, typeDefinitionsCount / 10) ? best : 0;
        }

        // A null slot must belong to a type with no fields, and every other slot must be a pointer.
        // Scoring "how pointer-like" the window is picks an interior hole of the real array.
        private int ScoreFieldOffsetsByCounts(byte[] image, uint addr, int[] counts)
        {
            if (addr + (ulong)counts.Length * 4 > (ulong)image.Length)
            {
                return 0;
            }
            var score = 0;
            for (var i = 0; i < counts.Length; i++)
            {
                var ptr = ReadU32(image, (int)addr + i * 4);
                if (counts[i] == 0)
                {
                    if (ptr == 0)
                    {
                        score++;
                    }
                }
                else if (ptr != 0 && (ptr & 3) == 0 && ptr <= (uint)image.Length - 4)
                {
                    score++;
                }
            }
            return score;
        }

        private bool TryFindMethodSpecs(byte[] image, int methodCount, uint fieldOffsets, out uint address, out int count, out int maxInstIndex)
        {
            address = 0;
            count = 0;
            maxInstIndex = -1;
            if (methodCount <= 0)
            {
                return false;
            }
            foreach (var addr in stride12Arrays)
            {
                if (addr + 12 > (uint)image.Length)
                {
                    continue;
                }
                var run = 0;
                var maxInst = -1;
                var cursor = addr;
                var limit = fieldOffsets != 0 && fieldOffsets > addr ? fieldOffsets : (uint)image.Length;
                while (cursor + 12 <= limit)
                {
                    var methodIndex = ReadI32(image, (int)cursor);
                    var classIndex = ReadI32(image, (int)cursor + 4);
                    var methodInst = ReadI32(image, (int)cursor + 8);
                    if (methodIndex < 0 || methodIndex >= methodCount || classIndex < -1 || methodInst < -1 || classIndex > 2_000_000 || methodInst > 2_000_000)
                    {
                        break;
                    }
                    if (classIndex > maxInst)
                    {
                        maxInst = classIndex;
                    }
                    if (methodInst > maxInst)
                    {
                        maxInst = methodInst;
                    }
                    run++;
                    cursor += 12;
                }
                if (run > count)
                {
                    count = run;
                    address = addr;
                    maxInstIndex = maxInst;
                }
            }
            return count >= 1000;
        }

        private uint FindGenericInsts(byte[] image, int minCount)
        {
            uint best = 0;
            var bestRun = 0;
            foreach (var addr in indexedPointerArrays)
            {
                var run = CountGenericInsts(image, addr);
                if (run > bestRun)
                {
                    bestRun = run;
                    best = addr;
                }
            }
            return bestRun >= minCount ? best : 0;
        }

        private int CountGenericInsts(byte[] image, uint addr)
        {
            if ((addr & 3) != 0 || addr >= image.Length)
            {
                return 0;
            }
            var count = 0;
            for (var cursor = addr; cursor + 4 <= (uint)image.Length; cursor += 4)
            {
                if (!IsGenericInst(image, ReadU32(image, (int)cursor)))
                {
                    break;
                }
                count++;
                if (count > 5_000_000)
                {
                    break;
                }
            }
            return count;
        }

        private static bool IsGenericInst(byte[] image, uint ptr)
        {
            if (ptr < 0x1000 || (ptr & 3) != 0 || ptr > (uint)image.Length - 8)
            {
                return false;
            }
            var argc = ReadI32(image, (int)ptr);
            var argv = ReadU32(image, (int)ptr + 4);
            if (argc < 1 || argc > 64 || (argv & 3) != 0 || argv > (uint)image.Length - 4)
            {
                return false;
            }
            return IsIl2CppTypePointer(image, ReadU32(image, (int)argv));
        }

        private int CountModules(byte[] image, uint addr, int imageCount)
        {
            if (addr + (ulong)imageCount * 4 > (ulong)image.Length)
            {
                return 0;
            }
            var count = 0;
            for (var i = 0; i < imageCount; i++)
            {
                if (IsCodeGenModule(image, ReadU32(image, (int)addr + i * 4)))
                {
                    count++;
                }
            }
            return count;
        }

        private static bool IsCodeGenModule(byte[] image, uint ptr)
        {
            if (ptr < 0x1000 || (ptr & 3) != 0 || ptr > (uint)image.Length - 12)
            {
                return false;
            }
            var namePtr = ReadU32(image, (int)ptr);
            var methodCount = ReadU32(image, (int)ptr + 4);
            var methodPointers = ReadU32(image, (int)ptr + 8);
            if (methodCount > 500000)
            {
                return false;
            }
            if (!IsCString(image, namePtr))
            {
                return false;
            }
            if (methodCount > 0 && (methodPointers < 0x1000 || methodPointers >= image.Length))
            {
                return false;
            }
            return true;
        }

        private static bool IsCString(byte[] image, uint addr)
        {
            if (addr < 0x100 || addr >= image.Length)
            {
                return false;
            }
            var length = 0;
            for (var i = (int)addr; i < image.Length && length < 160; i++, length++)
            {
                var c = image[i];
                if (c == 0)
                {
                    return length > 0;
                }
                if (c < 32 || c > 126)
                {
                    return false;
                }
            }
            return false;
        }

        private int CountTypeRun(byte[] image, uint addr)
        {
            if ((addr & 3) != 0 || addr >= image.Length)
            {
                return 0;
            }
            var count = 0;
            for (var cursor = addr; cursor + 4 <= (uint)image.Length; cursor += 4)
            {
                if (!IsIl2CppTypePointer(image, ReadU32(image, (int)cursor)))
                {
                    break;
                }
                count++;
                if (count > 5_000_000)
                {
                    break;
                }
            }
            return count;
        }

        private static bool IsIl2CppTypePointer(byte[] image, uint ptr)
        {
            if (ptr < 0x1000 || (ptr & 3) != 0 || ptr > (uint)image.Length - 8)
            {
                return false;
            }
            var bits = ReadU32(image, (int)ptr + 4);
            var typeEnum = (bits >> 16) & 0xFF;
            return typeEnum != 0 && (typeEnum <= 0x21 || typeEnum == 0x55);
        }

        private int ScoreFieldOffsets(byte[] image, uint addr, int typeDefinitionsCount)
        {
            if (addr + (ulong)typeDefinitionsCount * 4 > (ulong)image.Length)
            {
                return 0;
            }
            var strong = 0;
            for (var i = 0; i < typeDefinitionsCount; i++)
            {
                var ptr = ReadU32(image, (int)addr + i * 4);
                if (ptr == 0 || (ptr & 3) != 0 || ptr > (uint)image.Length - 8)
                {
                    continue;
                }
                var first = ReadI32(image, (int)ptr);
                if (first < 0 || first > 0x100 || (first & 3) != 0)
                {
                    continue;
                }
                var typeEnum = (ReadU32(image, (int)ptr + 4) >> 16) & 0xFF;
                if (typeEnum >= 1 && typeEnum <= 0x21)
                {
                    continue;
                }
                strong++;
            }
            return strong;
        }

        private void WriteCodeRegistration(uint realStart, uint imageCount, uint modules)
        {
            uint[] words =
            {
                0, // reversePInvokeWrapperCount
                0, // reversePInvokeWrappers
                0, // genericMethodPointersCount
                0, // genericMethodPointers
                Version31RealignmentMarker, // genericAdjustorThunks
                0, // invokerPointersCount
                0, // invokerPointers
                0, // unresolvedVirtualCallCount
                0, // unresolvedVirtualCallPointers
                0, // unresolvedInstanceCallPointers
                0, // unresolvedStaticCallPointers
                0, // interopDataCount
                0, // interopData
                0, // windowsRuntimeFactoryCount
                0, // windowsRuntimeFactoryTable
                imageCount,
                modules
            };
            Position = realStart;
            foreach (var word in words)
            {
                Write(word);
            }
        }

        private void WriteMetadataRegistration(uint addr, uint typesCount, uint types, uint fieldOffsetsCount, uint fieldOffsets, uint genericInstsCount, uint genericInsts, uint methodSpecsCount, uint methodSpecs)
        {
            uint[] words =
            {
                0, 0, // genericClasses
                genericInstsCount, genericInsts,
                0, 0, // genericMethodTable
                typesCount, types,
                methodSpecsCount, methodSpecs,
                fieldOffsetsCount, fieldOffsets,
                0, 0, // typeDefinitionsSizes
                0, 0  // metadataUsages
            };
            Position = addr;
            foreach (var word in words)
            {
                Write(word);
            }
        }

        private static System.Collections.Generic.IEnumerable<uint> FindPointers(byte[] image, uint target)
        {
            for (var i = 0; i + 4 <= image.Length; i += 4)
            {
                if (ReadU32(image, i) == target)
                {
                    yield return (uint)i;
                }
            }
        }

        private static uint ReadU32(byte[] image, int offset)
        {
            return BitConverter.ToUInt32(image, offset);
        }

        private static int ReadI32(byte[] image, int offset)
        {
            return BitConverter.ToInt32(image, offset);
        }
    }
}
