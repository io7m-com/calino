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

import java.util.Comparator;

/**
 * The declaration of a single mipmap.
 *
 * @param mipMapLevel      The mipmap level
 * @param layer            The layer
 * @param sizeCompressed   The size of the supercompressed data in octets
 * @param sizeUncompressed The size of the uncompressed data in octets
 * @param crc32            The CRC32 checksum of the uncompressed data
 */

public record CLNImageArrayMipMapDeclaration(
  int mipMapLevel,
  int layer,
  long sizeCompressed,
  long sizeUncompressed,
  int crc32)
  implements Comparable<CLNImageArrayMipMapDeclaration>
{
  @Override
  public int compareTo(
    final CLNImageArrayMipMapDeclaration other)
  {
    return ((Comparator<CLNImageArrayMipMapDeclaration>) (o1, o2) -> {
      return Integer.compareUnsigned(o1.mipMapLevel(), o2.mipMapLevel());
    }).reversed()
      .thenComparing((o1, o2) -> {
        return Integer.compareUnsigned(o1.layer(), o2.layer());
      }).compare(this, other);
  }
}
