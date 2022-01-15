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

package com.io7m.calino.supercompression.lz4;

import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIFactoryType;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIRequest;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIType;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIFactoryType;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIRequest;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIType;
import net.jpountz.lz4.LZ4Factory;
import net.jpountz.lz4.LZ4FrameInputStream;
import net.jpountz.lz4.LZ4FrameOutputStream;
import net.jpountz.xxhash.XXHashFactory;
import org.apache.commons.io.input.BoundedInputStream;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.channels.Channels;
import java.nio.channels.ReadableByteChannel;
import java.time.Duration;
import java.time.Instant;
import java.util.List;
import java.util.Objects;

/**
 * Support for LZ4 supercompression.
 */

public final class CLNSupercompressionLZ4
  implements CLNDecompressorSPIFactoryType, CLNCompressorSPIFactoryType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNSupercompressionLZ4.class);

  private static final List<CLNSuperCompressionMethodType> SUPPORTED =
    List.of(CLNSuperCompressionMethodStandard.LZ4);

  /**
   * Support for LZ4 supercompression.
   */

  public CLNSupercompressionLZ4()
  {

  }

  @Override
  public CLNCompressorSPIType createCompressor(
    final CLNCompressorSPIRequest request)
  {
    return new Compressor(request);
  }

  @Override
  public CLNDecompressorSPIType createDecompressor(
    final CLNDecompressorSPIRequest request)
    throws IOException
  {
    final var channelStream =
      Channels.newInputStream(request.channel());
    final var dataSize =
      request.imageDescription().dataSizeCompressed();
    final var boundedStream =
      new BoundedInputStream(channelStream, dataSize);

    final var decompressor =
      LZ4Factory.safeInstance()
        .safeDecompressor();

    final var lz4Stream =
      new LZ4FrameInputStream(
        boundedStream,
        decompressor,
        XXHashFactory.safeInstance().hash32()
      );

    return new Decompressor(Channels.newChannel(lz4Stream));
  }

  @Override
  public String name()
  {
    return CLNSupercompressionLZ4.class.getCanonicalName();
  }

  @Override
  public List<CLNSuperCompressionMethodType> supportedCompressionMethods()
  {
    return SUPPORTED;
  }

  @Override
  public List<CLNSuperCompressionMethodType> supportedDecompressionMethods()
  {
    return SUPPORTED;
  }

  private static final class Decompressor
    implements CLNDecompressorSPIType
  {
    private final ReadableByteChannel channel;

    private Decompressor(
      final ReadableByteChannel inChannel)
    {
      this.channel = Objects.requireNonNull(inChannel, "channel");
    }

    @Override
    public ReadableByteChannel decompressedData()
    {
      return this.channel;
    }
  }

  private static final class Compressor implements CLNCompressorSPIType
  {
    private final CLNCompressorSPIRequest request;

    Compressor(
      final CLNCompressorSPIRequest inRequest)
    {
      this.request = Objects.requireNonNull(inRequest, "request");
    }

    @Override
    public byte[] execute(
      final byte[] data)
      throws IOException
    {
      LOG.debug("compressing {} bytes", data.length);

      try (var byteStream = new ByteArrayOutputStream()) {
        final var timeThen = Instant.now();

        final var blockSize =
          LZ4FrameOutputStream.BLOCKSIZE.SIZE_4MB;
        final var compressor =
          LZ4Factory.safeInstance()
            .fastCompressor();
        final var hash32 =
          XXHashFactory.safeInstance().hash32();

        try (var lz4Stream = new LZ4FrameOutputStream(
          byteStream,
          blockSize,
          Integer.toUnsignedLong(data.length),
          compressor,
          hash32,
          LZ4FrameOutputStream.FLG.Bits.BLOCK_INDEPENDENCE)) {
          lz4Stream.write(data);
        }
        final var timeNow = Instant.now();
        final var ratio = (double) byteStream.size() / (double) data.length;
        final var percent = ratio * 100.0;

        LOG.debug(
          "compressed {} bytes to {} ({}%) in {}",
          data.length,
          byteStream.size(),
          String.format("%.2f", percent),
          Duration.between(timeThen, timeNow)
        );
        return byteStream.toByteArray();
      }
    }
  }
}
