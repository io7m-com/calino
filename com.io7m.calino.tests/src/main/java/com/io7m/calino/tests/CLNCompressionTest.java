/*
 * Copyright © 2021 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNSuperCompressionMethodCustom;
import com.io7m.calino.supercompression.api.CLNCompressorRequest;
import com.io7m.calino.supercompression.api.CLNCompressors;
import com.io7m.calino.supercompression.api.CLNDecompressorRequest;
import com.io7m.calino.supercompression.api.CLNDecompressors;
import com.io7m.calino.supercompression.deflate.CLNSupercompressionDEFLATE;
import com.io7m.calino.supercompression.lz4.CLNSupercompressionLZ4;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIRequest;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIRequest;
import com.io7m.wendover.core.ByteBufferChannels;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.channels.Channels;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.zip.CRC32;

import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.DEFLATE;
import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.LZ4;
import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public final class CLNCompressionTest
{
  @Test
  public void testUnsupportedCompression()
  {
    final var compressors = new CLNCompressors();

    assertThrows(
      UnsupportedOperationException.class, () -> {
        compressors.createCompressor(new CLNCompressorRequest(
          new CLNSuperCompressionMethodCustom("What?", 0L)
        ));
      });
  }

  @Test
  public void testUnsupportedDecompression()
  {
    final var decompressors = new CLNDecompressors();

    assertThrows(
      UnsupportedOperationException.class, () -> {
        decompressors.createDecompressor(new CLNDecompressorRequest(
          new CLNSuperCompressionMethodCustom("What?", 0L),
          new CLNImage2DDescription(
            0, 0L, 100L, 100L, 0
          ),
          ByteBufferChannels.ofByteBuffer(ByteBuffer.allocate(100))
        ));
      });
  }

  @Test
  public void testInflateDeflate(
    final @TempDir Path directory)
    throws IOException
  {
    final var resource =
      CLNTestDirectories.resourceOf(
        CLNCompressionTest.class,
        directory,
        "basic.ctf"
      );

    final var input =
      Files.readAllBytes(resource);

    final var crc32 = new CRC32();
    crc32.update(input);
    final var input32 =
      crc32.getValue();

    final var support =
      new CLNSupercompressionDEFLATE();

    final var compressor =
      support.createCompressor(new CLNCompressorSPIRequest(DEFLATE));

    final var compressed =
      compressor.execute(input);

    CLNHexDump.dumpTo(compressed, System.out);

    final var compressedBuffer = ByteBuffer.wrap(compressed);
    compressedBuffer.order(ByteOrder.nativeOrder());

    final var decompressor =
      support.createDecompressor(
        new CLNDecompressorSPIRequest(
          DEFLATE,
          new CLNImage2DDescription(
            0,
            0L,
            (long) input.length,
            (long) compressed.length,
            (int) input32
          ),
          ByteBufferChannels.ofByteBuffer(ByteBuffer.wrap(compressed))
        )
      );

    final var decompressedChannel =
      decompressor.decompressedData();
    final var decompressedStream =
      Channels.newInputStream(decompressedChannel);
    final var decompressedData =
      decompressedStream.readAllBytes();

    CLNHexDump.dumpTo(decompressedData, System.out);

    assertArrayEquals(
      decompressedData,
      input
    );
  }

  @Test
  public void testLZ4(
    final @TempDir Path directory)
    throws IOException
  {
    final var resource =
      CLNTestDirectories.resourceOf(
        CLNCompressionTest.class,
        directory,
        "basic.ctf"
      );

    final var input =
      Files.readAllBytes(resource);

    final var crc32 = new CRC32();
    crc32.update(input);
    final var input32 =
      crc32.getValue();

    final var support =
      new CLNSupercompressionLZ4();

    final var compressor =
      support.createCompressor(new CLNCompressorSPIRequest(LZ4));

    final var compressed =
      compressor.execute(input);

    CLNHexDump.dumpTo(compressed, System.out);

    final var compressedBuffer = ByteBuffer.wrap(compressed);
    compressedBuffer.order(ByteOrder.nativeOrder());

    final var decompressor =
      support.createDecompressor(
        new CLNDecompressorSPIRequest(
          LZ4,
          new CLNImage2DDescription(
            0,
            0L,
            (long) input.length,
            (long) compressed.length,
            (int) input32
          ),
          ByteBufferChannels.ofByteBuffer(ByteBuffer.wrap(compressed))
        )
      );

    final var decompressedChannel =
      decompressor.decompressedData();
    final var decompressedStream =
      Channels.newInputStream(decompressedChannel);
    final var decompressedData =
      decompressedStream.readAllBytes();

    CLNHexDump.dumpTo(decompressedData, System.out);

    assertArrayEquals(
      decompressedData,
      input
    );
  }
}
