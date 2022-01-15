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
import com.io7m.calino.imageproc.api.CLNImageView2DType;

import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.Objects;

/**
 * An unsigned 4444 view.
 */

public final class CLNImageView2DFixedU4444 implements CLNImageView2DType
{
  private static final int COMPONENT_SIZE = 2;
  private final ByteBuffer pixelData;
  private final CLNImageInfo imageInfo;
  private final int lineWidth;
  private final int pixelSize;

  /**
   * An unsigned 4444 view.
   *
   * @param inData      The image data
   * @param inImageInfo The image info
   */

  public CLNImageView2DFixedU4444(
    final CLNImageInfo inImageInfo,
    final byte[] inData)
  {
    this.imageInfo =
      Objects.requireNonNull(inImageInfo, "inImageInfo");

    this.pixelData = ByteBuffer.wrap(inData);
    this.pixelData.order(
      switch (inImageInfo.dataByteOrder()) {
        case LITTLE_ENDIAN -> ByteOrder.LITTLE_ENDIAN;
        case BIG_ENDIAN -> ByteOrder.BIG_ENDIAN;
      });

    this.pixelSize = COMPONENT_SIZE;
    this.lineWidth = this.imageInfo.sizeX() * this.pixelSize;
  }

  @Override
  public void pixelAt(
    final int x,
    final int y,
    final double[] pixel)
  {
    final var base = (y * this.lineWidth) + (x * this.pixelSize);
    final var data = ((int) this.pixelData.getShort(base)) & 0xffff;
    final var r = (data >> 12) & 0b1111;
    final var g = (data >> 8) & 0b1111;
    final var b = (data >> 4) & 0b1111;
    final var a = data & 0b1111;
    pixel[0] = (double) r / 15.0;
    pixel[1] = (double) g / 15.0;
    pixel[2] = (double) b / 15.0;
    pixel[3] = (double) a / 15.0;
  }
}
