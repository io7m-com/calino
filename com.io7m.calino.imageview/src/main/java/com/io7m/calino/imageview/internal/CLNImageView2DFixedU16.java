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
 * An unsigned fixed-point 16-bit view.
 */

public final class CLNImageView2DFixedU16 implements CLNImageView2DType
{
  private static final int COMPONENT_SIZE = 2;
  private final ByteBuffer pixelData;
  private final int componentCount;
  private final CLNImageInfo imageInfo;
  private final int lineWidth;
  private final int pixelSize;
  private final int sizeX;
  private final int sizeY;

  /**
   * An unsigned fixed-point 16-bit view.
   *
   * @param inComponentCount The component count
   * @param mipLevel         The mip level
   * @param inData           The image data
   * @param inImageInfo      The image info
   */

  public CLNImageView2DFixedU16(
    final CLNImageInfo inImageInfo,
    final int mipLevel,
    final byte[] inData,
    final int inComponentCount)
  {
    this.imageInfo =
      Objects.requireNonNull(inImageInfo, "inImageInfo");

    this.sizeX = inImageInfo.sizeX() >>> mipLevel;
    this.sizeY = inImageInfo.sizeY() >>> mipLevel;

    this.pixelData = ByteBuffer.wrap(inData);
    this.componentCount = inComponentCount;
    this.pixelData.order(
      switch (inImageInfo.dataByteOrder()) {
        case LITTLE_ENDIAN -> ByteOrder.LITTLE_ENDIAN;
        case BIG_ENDIAN -> ByteOrder.BIG_ENDIAN;
      });

    this.pixelSize = this.componentCount * COMPONENT_SIZE;
    this.lineWidth = this.sizeX * this.pixelSize;
  }

  @Override
  public int sizeX()
  {
    return this.sizeX;
  }

  @Override
  public int sizeY()
  {
    return this.sizeY;
  }

  @Override
  public void pixelAt(
    final int x,
    final int y,
    final double[] pixel)
  {
    final var base = (y * this.lineWidth) + (x * this.pixelSize);
    for (int index = 0; index < this.componentCount; ++index) {
      final var offset = index * COMPONENT_SIZE;
      final var c = ((int) this.pixelData.getShort(base + offset)) & 0xffff;
      pixel[index] = (double) c / 65535.0;
    }
  }
}
