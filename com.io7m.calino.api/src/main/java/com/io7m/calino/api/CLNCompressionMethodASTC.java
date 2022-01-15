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

/**
 * ASTC texture compression.
 */

public final class CLNCompressionMethodASTC
{
  private CLNCompressionMethodASTC()
  {

  }

  /**
   * Get the ASTC texture compression descriptor for the given block sizes.
   *
   * @param blockSizeX The size on the X axis
   * @param blockSizeY The size on the Y axis
   *
   * @return An ASTC texture compression descriptor
   */

  public static CLNCompressionMethodType get(
    final int blockSizeX,
    final int blockSizeY)
  {
    return new CLNCompressionMethodCustom(
      "ASTC",
      0L,
      blockSizeX,
      blockSizeY,
      16
    );
  }
}
