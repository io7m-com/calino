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

package com.io7m.calino.imageproc.api;

import com.io7m.calino.api.CLNByteOrder;

import java.nio.file.Path;
import java.util.Objects;
import java.util.Optional;

/**
 * The type of image processor requests.
 *
 * @param file             The input file
 * @param premultiplyAlpha {@code true} if images should be alpha premultiplied
 * @param targetByteOrder  The target byte order
 * @param layoutConversion The target image layout
 * @param generateMipMaps  If non-empty, mipmaps will be generated using this
 *                         filter
 */

public record CLNImageProcessorRequest(
  Path file,
  boolean premultiplyAlpha,
  CLNByteOrder targetByteOrder,
  Optional<CLNImageLayoutConversion> layoutConversion,
  Optional<CLNImageMipMapFilter> generateMipMaps)
{
  /**
   * The type of image processor requests.
   *
   * @param file             The input file
   * @param premultiplyAlpha {@code true} if images should be alpha
   *                         premultiplied
   * @param targetByteOrder  The target byte order
   * @param layoutConversion The target image layout
   * @param generateMipMaps  If non-empty, mipmaps will be generated using this
   *                         filter
   */

  public CLNImageProcessorRequest
  {
    Objects.requireNonNull(file, "file");
    Objects.requireNonNull(layoutConversion, "layoutConversion");
    Objects.requireNonNull(targetByteOrder, "targetByteOrder");
    Objects.requireNonNull(generateMipMaps, "generateMipMaps");
  }
}
