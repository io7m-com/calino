/*
 * Copyright © 2026 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

package com.io7m.calino.tests;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.channels.SeekableByteChannel;
import java.nio.file.Files;
import java.nio.file.Paths;

import static java.nio.file.StandardCopyOption.REPLACE_EXISTING;
import static java.nio.file.StandardOpenOption.READ;
import static java.nio.file.StandardOpenOption.WRITE;

public final class CLNValidationCaseCreation
{
  private static void writeAt32(
    final SeekableByteChannel channel,
    final long position,
    final int value)
    throws IOException
  {
    final var number = ByteBuffer.allocate(4);
    number.putInt(0, value);
    channel.position(position);
    channel.write(number);
  }

  private static void writeAt64(
    final SeekableByteChannel channel,
    final long position,
    final long value)
    throws IOException
  {
    final var number = ByteBuffer.allocate(8);
    number.putLong(0, value);
    channel.position(position);
    channel.write(number);
  }

  @Test
  public void testValidationCubeMipMapDisordered()
    throws Exception
  {
    makeTestCase(
      "cube-mipmaps.ctf",
      "validation-cube-mip-disordered.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt32(channel, 0x190L, 7);
      });
  }

  @Test
  public void testValidationCubeMipMapBadCRC32()
    throws Exception
  {
    makeTestCase(
      "cube-mipmaps.ctf",
      "validation-cube-crc-mismatch.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt32(channel, 0x478L, 0xaabbccdd);
      });
  }

  @Test
  public void testValidationCubeSizeUncompressedZero()
    throws Exception
  {
    makeTestCase(
      "cube-mipmaps.ctf",
      "validation-cube-size-uncompressed-zero.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt64(channel, 0x484L, 0L);
      });
  }

  @Test
  public void testValidationCubeUncompressedSizeMismatch()
    throws Exception
  {
    makeTestCase(
      "cube-mipmaps.ctf",
      "validation-cube-size-mismatch.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt64(channel, 0x484L, 13L);
      });
  }

  @Test
  public void testValidationCubeSizeCompressedZero()
    throws Exception
  {
    makeTestCase(
      "cube-mipmaps.ctf",
      "validation-cube-size-compressed-zero.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt64(channel, 0x48CL, 0L);
      });
  }

  @Test
  public void testValidationArrayMipNotUnique1()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-not-unique-1.ctf",
      (final SeekableByteChannel channel) -> {
        final var buffer = ByteBuffer.allocate(36);
        channel.position(0xE4L);
        channel.read(buffer);
        buffer.flip();
        channel.position(0x108L);
        channel.write(buffer);
      });
  }

  @Test
  public void testValidationArrayUncompressedSizeZero()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-uncompressed-size-zero.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt64(channel, 0xFCL, 0L);
      });
  }

  @Test
  public void testValidationArrayUncompressedSizeMismatch()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-uncompressed-size-mismatch.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt64(channel, 0xFCL, 193L);
      });
  }

  @Test
  public void testValidationArrayNoMipMaps()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-no-mipmaps.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt32(channel, 0xE0L, 0);
      });
  }

  @Test
  public void testValidationArrayMipNotUnique0()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-not-unique-0.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt32(channel, 0x10CL, 0);
        writeAt32(channel, 0x130L, 0);
      });
  }

  @Test
  public void testValidationArrayDisordered0()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-disordered-0.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt32(channel, 0x10CL, 2);
        writeAt32(channel, 0x130L, 1);
      });
  }

  @Test
  public void testValidationArrayLevelOutOfRange0()
    throws Exception
  {
    makeTestCase(
      "array-mipmaps.ctf",
      "validation-array-level-out-of-range-0.ctf",
      (final SeekableByteChannel channel) -> {
        writeAt32(channel, 0xE8L, 3);
        writeAt32(channel, 0x10CL, 2);
        writeAt32(channel, 0x130L, 1);
        writeAt32(channel, 0x154L, 0);
        writeAt32(channel, 0x178L, 1);
      });
  }

  @Test
  public void testValidationArrayLayersTooMany()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-layers-too-many.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(4);
        number.putInt(0, 2);
        channel.position(0x28L);
        channel.write(number);
      });
  }

  @Test
  public void testValidationArrayLayersTooFew()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-layers-too-few.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(4);
        number.putInt(0, 10);
        channel.position(0x28L);
        channel.write(number);
      });
  }

  @Test
  public void testValidationArrayIncorrectSize0()
    throws Exception
  {
    makeTestCase(
      "array-deflate.ctf",
      "validation-array-deflate-size-wrong-0.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(8);
        number.putLong(0, 23L);
        channel.position(0xFCL);
        channel.write(number);
      });
  }

  @Test
  public void testValidationArrayIncorrectSize1()
    throws Exception
  {
    makeTestCase(
      "array-deflate.ctf",
      "validation-array-deflate-size-wrong-1.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(8);
        number.putLong(0, 23L);
        channel.position(0xF4L);
        channel.write(number);
      });
  }

  @Test
  public void testValidationArrayIncorrectCRC32()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-crc-mismatch.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(4);
        number.putInt(0, 0xAABBCCDD);
        channel.position(0x104L);
        channel.write(number);
      });
  }

  @Test
  public void testValidationArrayImageOffsetZero()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-image-offset-zero.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(8);
        number.putLong(0, 0L);
        channel.position(0xECL);
        channel.write(number);
      });
  }

  @Test
  public void testValidationArrayCompressedSizeZero()
    throws Exception
  {
    makeTestCase(
      "array.ctf",
      "validation-array-compressed-size-zero.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(8);
        number.putLong(0, 0L);
        channel.position(0xFCL);
        channel.write(number);
      });
  }

  @Test
  public void testValidationCubeNoMipMaps()
    throws Exception
  {
    makeTestCase(
      "cube.ctf",
      "validation-cube-no-mipmaps.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(8);
        channel.position(0xE0L);
        channel.write(number);
      });
  }

  @Test
  public void testValidationCubeImageOffsetZero()
    throws Exception
  {
    makeTestCase(
      "cube.ctf",
      "validation-cube-image-offset-zero.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(8);
        channel.position(0xE8L);
        channel.write(number);
      });
  }

  @Test
  public void testValidationEndTrailing()
    throws Exception
  {
    makeTestCase(
      "fade32.ctf",
      "validation-end-trailing.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(8);
        number.putLong(0, 5L);
        channel.position(0x11C0L);
        channel.write(number);
      });
  }

  @Test
  public void testValidationEndSizeNonzero()
    throws Exception
  {
    makeTestCase(
      "fade32.ctf",
      "validation-end-nonzero.ctf",
      (final SeekableByteChannel channel) -> {
        final var number = ByteBuffer.allocate(8);
        number.putLong(0, 5L);
        channel.position(0x11B8L);
        channel.write(number);
      });
  }

  @Test
  public void testValidationNoEnd()
    throws Exception
  {
    makeTestCase(
      "fade32.ctf",
      "validation-end-missing.ctf",
      (final SeekableByteChannel channel) -> {
        channel.truncate(0x11B0L);
      });
  }

  @Test
  public void testValidation2DIncorrectSize0()
    throws Exception
  {
    makeTestCase(
      "fade32-deflate.ctf",
      "validation-2d-deflate-size-wrong-0.ctf",
      (final SeekableByteChannel channel) -> {
        final var mipmapIndex = ByteBuffer.allocate(8);
        mipmapIndex.putLong(0, 10L);
        channel.position(0x180L);
        channel.write(mipmapIndex);
      });
  }

  @Test
  public void testValidation2DIncorrectSize1()
    throws Exception
  {
    makeTestCase(
      "fade32-deflate.ctf",
      "validation-2d-deflate-size-wrong-1.ctf",
      (final SeekableByteChannel channel) -> {
        final var mipmapIndex = ByteBuffer.allocate(8);
        mipmapIndex.putLong(0, 128L);
        channel.position(0x188L);
        channel.write(mipmapIndex);
      });
  }

  @Test
  public void testValidation2DUncompressedSizeMismatch()
    throws Exception
  {
    makeTestCase(
      "fade32-mipmaps.ctf",
      "validation-2d-uncompressed-size-mismatch.ctf",
      (final SeekableByteChannel channel) -> {
        final var mipmapIndex = ByteBuffer.allocate(8);
        mipmapIndex.putLong(0, 13L);
        channel.position(0x188L);
        channel.write(mipmapIndex);
      });
  }

  @Test
  public void testValidation2DUncompressedSizeZero()
    throws Exception
  {
    makeTestCase(
      "fade32-mipmaps.ctf",
      "validation-2d-uncompressed-size-zero.ctf",
      (final SeekableByteChannel channel) -> {
        final var mipmapIndex = ByteBuffer.allocate(8);
        channel.position(0x180L);
        channel.write(mipmapIndex);
      });
  }

  @Test
  public void testValidation2DNoMipMaps()
    throws Exception
  {
    makeTestCase(
      "fade32-mipmaps.ctf",
      "validation-2d-no-mipmaps.ctf",
      (final SeekableByteChannel channel) -> {
        final var mipmapIndex = ByteBuffer.allocate(4);
        channel.position(0x170L);
        channel.write(mipmapIndex);
      });
  }

  @Test
  public void testValidation2DMipMapDisordered()
    throws Exception
  {
    makeTestCase(
      "fade32-mipmaps.ctf",
      "validation-2d-mip-disordered.ctf",
      (final SeekableByteChannel channel) -> {
        final var mipmapIndex = ByteBuffer.allocate(4);
        mipmapIndex.putInt(0, 1);
        channel.position(0x174L);
        channel.write(mipmapIndex);

        mipmapIndex.flip();
        mipmapIndex.putInt(0, 2);
        channel.position(0x194L);
        channel.write(mipmapIndex);

        mipmapIndex.flip();
        mipmapIndex.putInt(0, 3);
        channel.position(0x1B4L);
        channel.write(mipmapIndex);

        mipmapIndex.flip();
        mipmapIndex.putInt(0, 4);
        channel.position(0x1D4L);
        channel.write(mipmapIndex);

        mipmapIndex.flip();
        mipmapIndex.putInt(0, 5);
        channel.position(0x1F4L);
        channel.write(mipmapIndex);
      });
  }

  @Test
  public void testValidation2DMipMapDuplicate()
    throws Exception
  {
    makeTestCase(
      "fade32-mipmaps.ctf",
      "validation-2d-mip-duplicate.ctf",
      (final SeekableByteChannel channel) -> {
        final var mipmapIndex = ByteBuffer.allocate(4);
        mipmapIndex.putInt(0, 2);
        channel.position(0x194L);
        channel.write(mipmapIndex);
      });
  }

  @Test
  public void testValidation2DWrongZ()
    throws Exception
  {
    makeTestCase(
      "fade32.ctf",
      "validation-2d-wrong-size-z.ctf",
      (final SeekableByteChannel channel) -> {
        final var size = ByteBuffer.allocate(4);
        size.putInt(0, 23);
        channel.position(0x28L);
        channel.write(size);
      });
  }

  @Test
  public void testValidation2DCompressedSizeZero()
    throws Exception
  {
    makeTestCase(
      "fade32.ctf",
      "validation-2d-compressed-size-zero.ctf",
      (final SeekableByteChannel channel) -> {
        final var zero = ByteBuffer.allocate(8);
        channel.position(0x188L);
        channel.write(zero);
      });
  }

  @Test
  public void testValidation2DIncorrectCRC32()
    throws Exception
  {
    makeTestCase(
      "fade32.ctf",
      "validation-2d-crc-mismatch.ctf",
      (final SeekableByteChannel channel) -> {
        final var crc = ByteBuffer.allocate(4);
        crc.putInt(0, 0x20304050);
        channel.position(0x190L);
        channel.write(crc);
      });
  }

  @Test
  public void testValidation2DImageOffsetZero()
    throws Exception
  {
    makeTestCase(
      "fade32.ctf",
      "validation-2d-image-offset-zero.ctf",
      (final SeekableByteChannel channel) -> {
        final var offset = ByteBuffer.allocate(8);
        channel.position(0x178L);
        channel.write(offset);
      });
  }

  interface OpType
  {
    void process(SeekableByteChannel channel)
      throws Exception;
  }

  private static void makeTestCase(
    final String baseFile,
    final String outputFile,
    final OpType op)
    throws Exception
  {
    final var outputPath =
      Paths.get(outputFile);

    final var inputName =
      "/com/io7m/calino/tests/%s".formatted(baseFile);
    final var inputURL =
      CLNValidationCaseCreation.class.getResource(inputName);

    try (var stream = inputURL.openStream()) {
      Files.copy(stream, outputPath, REPLACE_EXISTING);
    }

    try (var channel = FileChannel.open(outputPath, WRITE, READ)) {
      op.process(channel);
      channel.force(true);
    }
  }
}
