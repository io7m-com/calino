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
 * An unsigned 565 view.
 */

public final class CLNImageView2DFixedU565
  extends CLNImageView2DRawAbstract16
{
  /**
   * An unsigned 565 view.
   *
   * @param inData      The image data
   * @param mipLevel    The mip level
   * @param inImageInfo The image info
   */

  public CLNImageView2DFixedU565(
    final CLNImageInfo inImageInfo,
    final int mipLevel,
    final byte[] inData)
  {
    super(
      inImageInfo,
      1,
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
    final var pixelSize =
      2;
    final var lineWidth =
      this.sizeX() * pixelSize;
    final var pixelData =
      this.pixelData();

    final var base = (y * lineWidth) + (x * pixelSize);
    final var data = ((int) pixelData.getShort(base)) & 0xffff;
    final var r = (data >>> 11) & 0b11111;
    final var g = (data >>> 5) & 0b111111;
    final var b = data & 0b11111;
    pixel[0] = (double) r / 31.0;
    pixel[1] = (double) g / 63.0;
    pixel[2] = (double) b / 31.0;
  }
}
