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

package com.io7m.calino.imageview.internal;

import com.io7m.calino.api.CLNImageInfo;

/**
 * An unsigned fixed-point 8-bit view.
 */

public final class CLNImageView2DFixedU8
  extends CLNImageView2DRawAbstract8
{
  /**
   * An unsigned fixed-point 8-bit view.
   *
   * @param inComponentCount The component count
   * @param mipLevel         The mip level
   * @param inData           The image data
   * @param inImageInfo      The image info
   */

  public CLNImageView2DFixedU8(
    final CLNImageInfo inImageInfo,
    final int mipLevel,
    final byte[] inData,
    final int inComponentCount)
  {
    super(
      inImageInfo,
      inComponentCount,
      mipLevel,
      inData
    );
  }

  @Override
  public void pixelAt(
    final int x,
    final int y,
    final double[] pixel)
  {
    final var data =
      this.pixelData();
    final var componentCount =
      this.componentCount();
    final var rowWidth =
      componentCount * this.sizeX();

    final var base = (y * rowWidth) + (x * componentCount);
    for (var index = 0; index < componentCount; ++index) {
      final var c = ((int) data.get(base + index)) & 0xff;
      pixel[index] = (double) c / 255.0;
    }
  }
}
