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

import java.util.HashSet;
import java.util.List;
import java.util.Objects;

/**
 * A set of mipmap declarations.
 *
 * @param mipMaps             The set of mipmaps
 * @param texelBlockAlignment The required alignment of the texel data
 *
 * @see CLNImageInfo#texelBlockAlignment()
 */

public record CLNImage2DMipMapDeclarations(
  List<CLNImage2DMipMapDeclaration> mipMaps,
  int texelBlockAlignment)
{
  /**
   * A set of mipmap declarations.
   *
   * @param mipMaps             The set of mipmaps
   * @param texelBlockAlignment The required alignment of the texel data
   *
   * @see CLNImageInfo#texelBlockAlignment()
   */

  public CLNImage2DMipMapDeclarations
  {
    Objects.requireNonNull(mipMaps, "mipMaps");
    checkMipMaps(mipMaps);
  }

  private static void checkMipMaps(
    final List<CLNImage2DMipMapDeclaration> mipMaps)
  {
    final var mipLevelSet = new HashSet<Integer>(mipMaps.size());
    var mipHighest = 0;
    for (final var mipMap : mipMaps) {
      mipLevelSet.add(mipMap.mipMapLevel());
      mipHighest = Math.max(mipHighest, mipMap.mipMapLevel());
    }

    for (int mipLevel = 0; mipLevel < mipHighest; ++mipLevel) {
      if (!mipLevelSet.contains(mipLevel)) {
        throw new IllegalArgumentException(
          String.format(
            "Mip levels must be strictly increasing with all values present in the range [%d, %d]",
            0,
            mipHighest)
        );
      }
    }
  }
}
