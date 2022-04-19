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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A set of mipmap declarations.
 *
 * @param mipMaps             The set of mipmaps
 * @param texelBlockAlignment The required alignment of the texel data
 *
 * @see CLNImageInfo#texelBlockAlignment()
 */

public record CLNImageArrayMipMapDeclarations(
  List<CLNImageArrayMipMapDeclaration> mipMaps,
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

  public CLNImageArrayMipMapDeclarations
  {
    Objects.requireNonNull(mipMaps, "mipMaps");
    checkMipMaps(mipMaps);
  }

  private static void checkMipMaps(
    final List<CLNImageArrayMipMapDeclaration> mipMaps)
  {
    final var mips =
      new HashMap<Integer, Map<Integer, CLNImageArrayMipMapDeclaration>>(
        mipMaps.size());

    var mipHighest = 0;
    var layerHighest = 0;

    for (final var mipMap : mipMaps) {
      final var level = mipMap.mipMapLevel();
      final var layer = mipMap.layer();

      var layers = mips.get(level);
      if (layers == null) {
        layers = new HashMap<>();
      }
      if (layers.containsKey(layer)) {
        throw new IllegalArgumentException(
          String.format("Mip level %d layer %d is not unique", level, layer)
        );
      }

      layers.put(layer, mipMap);
      mips.put(level, layers);
      mipHighest = Math.max(mipHighest, level);
      layerHighest = Math.max(layerHighest, layer);
    }

    for (int mipLevel = 0; mipLevel <= mipHighest; ++mipLevel) {
      final var layers = mips.get(mipLevel);
      if (layers == null) {
        throw new IllegalArgumentException(
          String.format(
            "Mip levels must be strictly increasing with all values present in the range [%d, %d]",
            0,
            mipHighest)
        );
      }

      for (int layer = 0; layer <= layerHighest; ++layer) {
        if (!layers.containsKey(layer)) {
          throw new IllegalArgumentException(
            String.format(
              "Mip layers for level %d must be strictly increasing with all values present in the range [%d, %d]",
              mipLevel,
              0,
              layerHighest)
          );
        }
      }
    }

    final var sorted =
      mipMaps.stream()
        .sorted()
        .toList();

    if (!Objects.equals(sorted, mipMaps)) {
      throw new IllegalArgumentException(
        "Array image mipmaps must be provided in sorted order!");
    }
  }
}
