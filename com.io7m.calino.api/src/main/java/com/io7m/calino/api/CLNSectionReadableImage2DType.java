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

package com.io7m.calino.api;

import java.io.IOException;
import java.nio.channels.ReadableByteChannel;
import java.nio.channels.SeekableByteChannel;
import java.util.List;

/**
 * A readable 2D image section.
 */

public non-sealed interface CLNSectionReadableImage2DType
  extends CLNSectionReadableStandardType
{
  /**
   * @return The set of declared mipmaps
   *
   * @throws IOException On errors
   */

  List<CLNImage2DDescription> mipMapDescriptions()
    throws IOException;

  /**
   * Obtain a readable channel that returns decompressed data (that is, data
   * with any supercompression removed).
   *
   * @param description The image description
   *
   * @return A readable channel
   *
   * @throws IOException On I/O errors
   */

  ReadableByteChannel mipMapDataWithoutSupercompression(
    CLNImage2DDescription description)
    throws IOException;

  /**
   * Obtain a readable channel that returns potentially compressed data. The
   * bytes returned by the channel are not interpreted in any form, and are
   * exactly as they appeared in the underlying file.
   *
   * @param description The image description
   *
   * @return A readable channel
   *
   * @throws IOException On I/O errors
   */

  SeekableByteChannel mipMapDataRaw(
    CLNImage2DDescription description)
    throws IOException;
}
