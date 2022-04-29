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
import java.util.Objects;

/**
 * The declaration of a single cube mipmap.
 *
 * @param mipMapLevel The mipmap level
 * @param xPositive   The positive X face
 * @param xNegative   The negative X face
 * @param yPositive   The positive Y face
 * @param yNegative   The negative Y face
 * @param zPositive   The positive Z face
 * @param zNegative   The negative Z face
 */

public record CLNImageCubeMipMapDeclaration(
  int mipMapLevel,
  CLNImageCubeFaceDeclaration xPositive,
  CLNImageCubeFaceDeclaration xNegative,
  CLNImageCubeFaceDeclaration yPositive,
  CLNImageCubeFaceDeclaration yNegative,
  CLNImageCubeFaceDeclaration zPositive,
  CLNImageCubeFaceDeclaration zNegative
) implements Comparable<CLNImageCubeMipMapDeclaration>
{
  /**
   * The declaration of a single cube mipmap.
   *
   * @param mipMapLevel The mipmap level
   * @param xPositive   The positive X face
   * @param xNegative   The negative X face
   * @param yPositive   The positive Y face
   * @param yNegative   The negative Y face
   * @param zPositive   The positive Z face
   * @param zNegative   The negative Z face
   */

  public CLNImageCubeMipMapDeclaration
  {
    Objects.requireNonNull(xPositive, "xPositive");
    Objects.requireNonNull(xNegative, "xNegative");
    Objects.requireNonNull(yPositive, "yPositive");
    Objects.requireNonNull(yNegative, "yNegative");
    Objects.requireNonNull(zPositive, "zPositive");
    Objects.requireNonNull(zNegative, "zNegative");
  }

  @Override
  public int compareTo(
    final CLNImageCubeMipMapDeclaration other)
  {
    return ((Comparator<CLNImageCubeMipMapDeclaration>) (o1, o2) -> {
      return Integer.compareUnsigned(o1.mipMapLevel(), o2.mipMapLevel());
    }).reversed()
      .compare(this, other);
  }
}
