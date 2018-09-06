/*
 * This file is part of regionfile, licensed under the MIT License.
 *
 * Copyright (c) 2018 KyoriPowered
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package net.kyori.regionfile;

import org.checkerframework.checker.nullness.qual.Nullable;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Path;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.zip.DeflaterOutputStream;
import java.util.zip.GZIPInputStream;
import java.util.zip.InflaterInputStream;

/*
 ** 2011 January 5
 **
 ** The author disclaims copyright to this source code.  In place of
 ** a legal notice, here is a blessing:
 **
 **    May you do good and not evil.
 **    May you find forgiveness for yourself and forgive others.
 **    May you share freely, never taking more than you give.
 **/

/*
 * 2011 February 16
 *
 * This source code is based on the work of Scaevolus (see notice above).
 * It has been slightly modified by Mojang AB (constants instead of magic
 * numbers, a chunk timestamp header, and auto-formatted according to our
 * formatter template).
 *
 */

// Interfaces with region files on the disk

/*
 Region File Format
 Concept: The minimum unit of storage on hard drives is 4KB. 90% of Minecraft
 chunks are smaller than 4KB. 99% are smaller than 8KB. Write a simple
 container to store chunks in single files in runs of 4KB sectors.
 Each region file represents a 32x32 group of chunks. The conversion from
 chunk number to region number is floor(coord / 32): a chunk at (30, -3)
 would be in region (0, -1), and one at (70, -30) would be at (3, -1).
 Region files are named "r.x.z.data", where x and z are the region coordinates.
 A region file begins with a 4KB header that describes where chunks are stored
 in the file. A 4-byte big-endian integer represents sector offsets and sector
 counts. The chunk offset for a chunk (x, z) begins at byte 4*(x+z*32) in the
 file. The bottom byte of the chunk offset indicates the number of sectors the
 chunk takes up, and the top 3 bytes represent the sector number of the chunk.
 Given a chunk offset o, the chunk data begins at byte 4096*(o/256) and takes up
 at most 4096*(o%256) bytes. A chunk cannot exceed 1MB in size. If a chunk
 offset is 0, the corresponding chunk is not stored in the region file.
 Chunk data begins with a 4-byte big-endian integer representing the chunk data
 length in bytes, not counting the length field. The length must be smaller than
 4096 times the number of sectors. The next byte is a version field, to allow
 backwards-compatible updates to how chunks are encoded.
 A version of 1 represents a gzipped NBT file. The gzipped data is the chunk
 length - 1.
 A version of 2 represents a deflated (zlib compressed) NBT file. The deflated
 data is the chunk length - 1.
 */

public class RegionFile implements AutoCloseable {
  private static final int VERSION_GZIP = 1;
  private static final int VERSION_DEFLATE = 2;

  private static final int SECTOR_BYTES = 4096;
  private static final int SECTOR_INTS = SECTOR_BYTES / 4;
  private static final byte[] EMPTY_SECTOR = new byte[SECTOR_BYTES];

  static final int CHUNK_HEADER_SIZE = 5;

  private final int[] offsets = new int[SECTOR_INTS];
  private final int[] chunkTimestamps = new int[SECTOR_INTS];
  private final RandomAccessFile file;
  private final List<Boolean> sectorFree;
  private int sizeDelta;
  private long lastModified;

  public RegionFile(final Path path) throws IOException {
    this(path.toFile());
  }

  public RegionFile(final File file) throws IOException {
    if(file.exists()) {
      this.lastModified = file.lastModified();
    }

    this.file = new RandomAccessFile(file, "rw"); // read + write

    if(this.file.length() < SECTOR_BYTES) {
      this.file.write(EMPTY_SECTOR); // offsets
      this.file.write(EMPTY_SECTOR); // chunk timestamps
      this.sizeDelta += SECTOR_BYTES * 2;
    }

    if((this.file.length() & 0xfff) != 0) {
      // the file size is not a multiple of 4KB, grow it
      for(int i = 0; i < (this.file.length() & 0xfff); i++) {
        this.file.write(0);
      }
    }

    final int nSectors = (int) this.file.length() / SECTOR_BYTES;
    this.sectorFree = new ArrayList<>(nSectors);

    for(int i = 0; i < nSectors; i++) {
      this.sectorFree.add(true);
    }

    this.sectorFree.set(0, false); // chunk offset table
    this.sectorFree.set(1, false); // for the last modified info

    this.file.seek(0);

    for(int i = 0; i < SECTOR_INTS; i++) {
      final int offset = this.file.readInt();
      this.offsets[i] = offset;
      if(offset != 0 && (offset >> 8) + (offset & 0xff) <= this.sectorFree.size()) {
        for(int sectorNum = 0; sectorNum < (offset & 0xff); ++sectorNum) {
          this.sectorFree.set((offset >> 8) + sectorNum, false);
        }
      }
    }

    for(int i = 0; i < SECTOR_INTS; i++) {
      final int lastModValue = this.file.readInt();
      this.chunkTimestamps[i] = lastModValue;
    }
  }

  public synchronized @Nullable DataInputStream read(final int x, final int z) throws IOException {
    if(outOfBounds(x, z)) {
      return null;
    }

    final int offset = this.getOffset(x, z);
    if(offset == 0) {
      return null;
    }

    final int sectorNumber = offset >> 8;
    final int numSectors = offset & 0xff;
    if(sectorNumber + numSectors > this.sectorFree.size()) {
      return null;
    }

    this.file.seek(sectorNumber * SECTOR_BYTES);

    final int length = this.file.readInt();
    if(length > SECTOR_BYTES * numSectors) {
      return null;
    } else if(length <= 0) {
      return null;
    }

    final byte version = this.file.readByte();
    if(version == VERSION_GZIP) {
      final byte[] data = new byte[length - 1];
      this.file.read(data);
      return new DataInputStream(new BufferedInputStream(new GZIPInputStream(new ByteArrayInputStream(data))));
    } else if(version == VERSION_DEFLATE) {
      final byte[] data = new byte[length - 1];
      this.file.read(data);
      return new DataInputStream(new BufferedInputStream(new InflaterInputStream(new ByteArrayInputStream(data))));
    }

    return null;
  }

  public @Nullable DataOutputStream write(final int x, final int z) {
    if(outOfBounds(x, z)) {
      return null;
    }
    return new DataOutputStream(new BufferedOutputStream(new DeflaterOutputStream(new ChunkBuffer(x, z))));
  }

  protected synchronized void write(final int x, final int z, final byte[] data, final int length) throws IOException {
    final int offset = this.getOffset(x, z);
    int sectorNumber = offset >> 8;
    final int sectorsAllocated = offset & 0xFF;
    final int sectorsNeeded = (length + CHUNK_HEADER_SIZE) / SECTOR_BYTES + 1;

    // maximum chunk size is 1MB
    if(sectorsNeeded >= 256) {
      return;
    }

    if(sectorNumber != 0 && sectorsAllocated == sectorsNeeded) {
      this.write(sectorNumber, data, length);
    } else {
      // mark the sectors previously used for this chunk as free
      for(int i = 0; i < sectorsAllocated; ++i) {
        this.sectorFree.set(sectorNumber + i, true);
      }

      // scan for a free space large enough to store this chunk
      int runStart = this.sectorFree.indexOf(true);
      int runLength = 0;
      if(runStart != -1) {
        for(int i = runStart; i < this.sectorFree.size(); ++i) {
          if(runLength != 0) {
            if(this.sectorFree.get(i)) {
              runLength++;
            } else {
              runLength = 0;
            }
          } else if(this.sectorFree.get(i)) {
            runStart = i;
            runLength = 1;
          }
          if(runLength >= sectorsNeeded) {
            break;
          }
        }
      }

      if(runLength >= sectorsNeeded) {
        // we found a free space large enough
        sectorNumber = runStart;
        this.setOffset(x, z, (sectorNumber << 8) | sectorsNeeded);
        for(int i = 0; i < sectorsNeeded; ++i) {
          this.sectorFree.set(sectorNumber + i, false);
        }
        this.write(sectorNumber, data, length);
      } else {
        // no free space large enough found -- we need to grow the file
        this.file.seek(this.file.length());
        sectorNumber = this.sectorFree.size();
        for(int i = 0; i < sectorsNeeded; ++i) {
          this.file.write(EMPTY_SECTOR);
          this.sectorFree.add(false);
        }
        this.sizeDelta += SECTOR_BYTES * sectorsNeeded;

        this.write(sectorNumber, data, length);
        this.setOffset(x, z, (sectorNumber << 8) | sectorsNeeded);
      }
    }

    this.setTimestamp(x, z, (int) (Instant.now().toEpochMilli() / 1000L));
  }

  private void write(final int sectorNumber, final byte[] data, final int length) throws IOException {
    this.file.seek(sectorNumber * SECTOR_BYTES);
    this.file.writeInt(length + 1); // chunk length
    this.file.writeByte(VERSION_DEFLATE); // chunk version number
    this.file.write(data, 0, length); // chunk data
  }

  private int getOffset(final int x, final int z) {
    return this.offsets[x + z * 32];
  }

  private void setOffset(final int x, final int z, final int offset) throws IOException {
    this.offsets[x + z * 32] = offset;
    this.file.seek((x + z * 32) * 4);
    this.file.writeInt(offset);
  }

  private void setTimestamp(final int x, final int z, final int value) throws IOException {
    this.chunkTimestamps[x + z * 32] = value;
    this.file.seek(SECTOR_BYTES + (x + z * 32) * 4);
    this.file.writeInt(value);
  }

  private static boolean outOfBounds(final int x, final int z) {
    return x < 0 || x >= 32 || z < 0 || z >= 32;
  }

  @Override
  public void close() throws IOException {
    if(this.file != null) {
      this.file.close();
    }
  }

  class ChunkBuffer extends ByteArrayOutputStream {
    private final int x;
    private final int z;

    ChunkBuffer(final int x, final int z) {
      super(8096); // initialize to 8KB
      this.x = x;
      this.z = z;
    }

    @Override
    public void close() throws IOException {
      RegionFile.this.write(this.x, this.z, this.buf, this.count);
    }
  }
}
