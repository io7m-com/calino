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

package com.io7m.calino.supercompression.spi;

import com.io7m.calino.api.CLNSuperCompressionMethodType;

import java.io.IOException;
import java.util.List;

/**
 * The type of decompressor factories.
 */

public interface CLNDecompressorSPIFactoryType
{
  /**
   * Determine if a compression method is supported.
   *
   * @param method The compression method
   *
   * @return {@code true} if the compression method is supported
   */

  default boolean supportsDecompressionFor(
    final CLNSuperCompressionMethodType method)
  {
    return this.supportedDecompressionMethods()
      .contains(method);
  }

  /**
   * Create a decompressor.
   *
   * @param request The decompression request
   *
   * @return A decompressor
   *
   * @throws IOException On errors
   */

  CLNDecompressorSPIType createDecompressor(
    CLNDecompressorSPIRequest request)
    throws IOException;

  /**
   * @return The name of the factory implementation
   */

  String name();

  /**
   * @return The list of the supported compression methods
   */

  List<CLNSuperCompressionMethodType> supportedDecompressionMethods();
}
