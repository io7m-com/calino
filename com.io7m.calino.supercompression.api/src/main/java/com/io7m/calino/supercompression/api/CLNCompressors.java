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

package com.io7m.calino.supercompression.api;

import com.io7m.calino.supercompression.spi.CLNCompressorSPIFactoryType;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIRequest;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIType;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.ServiceLoader;

/**
 * A factory of compressors.
 */

public final class CLNCompressors implements CLNCompressorFactoryType
{
  private final List<CLNCompressorSPIFactoryType> compressors;

  /**
   * A factory of compressors.
   *
   * @param inDecompressors The compressors
   */

  public CLNCompressors(
    final List<CLNCompressorSPIFactoryType> inDecompressors)
  {
    this.compressors =
      List.copyOf(
        Objects.requireNonNull(inDecompressors, "compressors"));
  }

  /**
   * A factory of compressors.
   */

  public CLNCompressors()
  {
    this(fromServiceLoader());
  }

  private static List<CLNCompressorSPIFactoryType> fromServiceLoader()
  {
    final var loader =
      ServiceLoader.load(CLNCompressorSPIFactoryType.class);
    final var iterator =
      loader.iterator();
    final var compressors =
      new ArrayList<CLNCompressorSPIFactoryType>();

    while (iterator.hasNext()) {
      compressors.add(iterator.next());
    }
    return compressors;
  }

  @Override
  public CLNCompressorType createCompressor(
    final CLNCompressorRequest request)
    throws IOException
  {
    final var spiRequest =
      new CLNCompressorSPIRequest(
        request.method()
      );

    for (final var compressorFactory : this.compressors) {
      if (compressorFactory.supportsCompressionFor(request.method())) {
        return new Compressor(
          compressorFactory.createCompressor(spiRequest));
      }
    }

    final var lineSeparator = System.lineSeparator();
    final var message = new StringBuilder(128);
    message.append("No available support for compression method.");
    message.append(lineSeparator);
    message.append("  Compression method: ");
    message.append(request.method().descriptor());
    message.append(lineSeparator);

    if (!this.compressors.isEmpty()) {
      message.append("  Available support:");
      message.append(lineSeparator);

      var index = 0;
      for (final var compressor : this.compressors) {
        for (final var method : compressor.supportedCompressionMethods()) {
          message.append("  [");
          message.append(index);
          message.append("] ");
          message.append(compressor.name());
          message.append(' ');
          message.append(method.descriptor());
          message.append(lineSeparator);
          ++index;
        }
      }
    } else {
      message.append("  No available compressor services!");
      message.append(lineSeparator);
    }

    throw new UnsupportedOperationException(message.toString());
  }

  private static final class Compressor implements CLNCompressorType
  {
    private final CLNCompressorSPIType compressor;

    Compressor(
      final CLNCompressorSPIType inDecompressor)
    {
      this.compressor =
        Objects.requireNonNull(inDecompressor, "compressor");
    }

    @Override
    public byte[] execute(final byte[] data)
      throws IOException
    {
      Objects.requireNonNull(data, "data");
      return this.compressor.execute(data);
    }
  }
}
