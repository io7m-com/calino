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

import com.io7m.calino.supercompression.spi.CLNDecompressorSPIFactoryType;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIRequest;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIType;

import java.io.IOException;
import java.nio.channels.ReadableByteChannel;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.ServiceLoader;

/**
 * A factory of decompressors.
 */

public final class CLNDecompressors implements CLNDecompressorFactoryType
{
  private final List<CLNDecompressorSPIFactoryType> decompressors;

  /**
   * A factory of decompressors.
   *
   * @param inDecompressors The decompressors
   */

  public CLNDecompressors(
    final List<CLNDecompressorSPIFactoryType> inDecompressors)
  {
    this.decompressors =
      List.copyOf(
        Objects.requireNonNull(inDecompressors, "decompressors"));
  }

  /**
   * A factory of decompressors.
   */

  public CLNDecompressors()
  {
    this(fromServiceLoader());
  }

  private static List<CLNDecompressorSPIFactoryType> fromServiceLoader()
  {
    final var loader =
      ServiceLoader.load(CLNDecompressorSPIFactoryType.class);
    final var iterator =
      loader.iterator();
    final var decompressors =
      new ArrayList<CLNDecompressorSPIFactoryType>();

    while (iterator.hasNext()) {
      decompressors.add(iterator.next());
    }
    return decompressors;
  }

  @Override
  public CLNDecompressorType createDecompressor(
    final CLNDecompressorRequest request)
    throws IOException
  {
    final var spiRequest =
      new CLNDecompressorSPIRequest(
        request.method(),
        request.imageDescription(),
        request.channel()
      );

    for (final var decompressorFactory : this.decompressors) {
      if (decompressorFactory.supportsDecompressionFor(request.method())) {
        return new Decompressor(
          decompressorFactory.createDecompressor(spiRequest));
      }
    }

    final var lineSeparator = System.lineSeparator();
    final var message = new StringBuilder(128);
    message.append("No available support for compression method.");
    message.append(lineSeparator);
    message.append("  Compression method: ");
    message.append(request.method().descriptor());
    message.append(lineSeparator);

    if (!this.decompressors.isEmpty()) {
      message.append("  Available support:");
      message.append(lineSeparator);

      var index = 0;
      for (final var decompressor : this.decompressors) {
        for (final var method : decompressor.supportedDecompressionMethods()) {
          message.append("  [");
          message.append(index);
          message.append("] ");
          message.append(decompressor.name());
          message.append(' ');
          message.append(method.descriptor());
          message.append(lineSeparator);
          ++index;
        }
      }
    } else {
      message.append("  No available decompressor services!");
      message.append(lineSeparator);
    }

    throw new UnsupportedOperationException(message.toString());
  }

  private static final class Decompressor implements CLNDecompressorType
  {
    private final CLNDecompressorSPIType decompressor;

    Decompressor(
      final CLNDecompressorSPIType inDecompressor)
    {
      this.decompressor =
        Objects.requireNonNull(inDecompressor, "decompressor");
    }

    @Override
    public ReadableByteChannel decompressedData()
    {
      return this.decompressor.decompressedData();
    }
  }
}
