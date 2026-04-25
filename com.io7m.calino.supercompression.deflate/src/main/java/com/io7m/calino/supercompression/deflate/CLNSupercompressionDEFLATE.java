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

package com.io7m.calino.supercompression.deflate;

import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIFactoryType;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIRequest;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIType;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIFactoryType;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIRequest;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIType;
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
import java.util.zip.Deflater;
import java.util.zip.DeflaterOutputStream;
import java.util.zip.Inflater;
import java.util.zip.InflaterInputStream;

import static java.util.zip.Deflater.BEST_COMPRESSION;

/**
 * Support for DEFLATE supercompression.
 */

public final class CLNSupercompressionDEFLATE
  implements CLNDecompressorSPIFactoryType, CLNCompressorSPIFactoryType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNSupercompressionDEFLATE.class);

  private static final List<CLNSuperCompressionMethodType> SUPPORTED =
    List.of(CLNSuperCompressionMethodStandard.DEFLATE);

  /**
   * Support for DEFLATE supercompression.
   */

  public CLNSupercompressionDEFLATE()
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
      BoundedInputStream.builder()
        .setInputStream(channelStream)
        .setMaxCount(dataSize)
        .get();

    final var inflater =
      new Inflater();
    final var inflateInput =
      new InflaterInputStream(boundedStream, inflater);

    return new Decompressor(Channels.newChannel(inflateInput));
  }

  @Override
  public String name()
  {
    return CLNSupercompressionDEFLATE.class.getCanonicalName();
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
      LOG.debug("Compressing {} bytes", data.length);

      try (var byteStream = new ByteArrayOutputStream()) {
        final var timeThen = Instant.now();

        final var deflater = new Deflater(BEST_COMPRESSION);
        try (var deflaterOutput = new DeflaterOutputStream(byteStream, deflater)) {
          deflaterOutput.write(data);
          deflaterOutput.finish();
          deflaterOutput.flush();
        }

        final var timeNow = Instant.now();
        final var ratio = (double) byteStream.size() / (double) data.length;
        final var percent = ratio * 100.0;

        LOG.debug(
          "Compressed {} bytes to {} ({}%) in {}",
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
