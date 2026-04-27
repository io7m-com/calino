/*
 * Copyright © 2026 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

import com.io7m.calino.api.CLNByteOrder;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.imageproc.api.CLNImageView2DType;

import java.lang.foreign.MemorySegment;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.Objects;

abstract class CLNImageView2DRawAbstract
  implements CLNImageView2DType
{
  private static final int LARGEST_PIXEL_SIZE = 4 * 8;

  private final ByteBuffer pixelData;
  private final CLNImageInfo imageInfo;
  private final int sizeX;
  private final int sizeY;

  protected CLNImageView2DRawAbstract(
    final CLNImageInfo inImageInfo,
    final ByteBuffer inPixelData,
    final int mipLevel)
  {
    this.imageInfo =
      Objects.requireNonNull(inImageInfo, "ImageInfo");
    this.pixelData =
      Objects.requireNonNull(inPixelData, "PixelData");

    this.sizeX =
      inImageInfo.sizeX() >>> mipLevel;
    this.sizeY =
      inImageInfo.sizeY() >>> mipLevel;

    this.pixelData.order(
      switch (inImageInfo.dataByteOrder()) {
        case LITTLE_ENDIAN -> ByteOrder.LITTLE_ENDIAN;
        case BIG_ENDIAN -> ByteOrder.BIG_ENDIAN;
      });
  }

  @Override
  public final byte[] pixelRawAt(
    final int x,
    final int y)
  {
    return this.pixelRawAtOrdered(x, y, this.imageInfo.dataByteOrder());
  }

  protected final ByteBuffer pixelData()
  {
    return this.pixelData;
  }

  protected final CLNImageInfo imageInfo()
  {
    return this.imageInfo;
  }

  @Override
  public final int sizeX()
  {
    return this.sizeX;
  }

  @Override
  public final int sizeY()
  {
    return this.sizeY;
  }

  @Override
  public final int pixelRawAt(
    final int x,
    final int y,
    final byte[] output)
  {
    return this.pixelRawAtOrdered(x, y, this.imageInfo.dataByteOrder(), output);
  }

  @Override
  public final void copyTo(
    final MemorySegment segment,
    final CLNByteOrder byteOrder)
  {
    final var segmentBuffer = segment.asByteBuffer();
    segmentBuffer.order(
      switch (byteOrder) {
        case BIG_ENDIAN -> ByteOrder.BIG_ENDIAN;
        case LITTLE_ENDIAN -> ByteOrder.LITTLE_ENDIAN;
      }
    );

    final var pixelBuffer = new byte[LARGEST_PIXEL_SIZE];
    for (int y = 0; y < this.sizeY; ++y) {
      for (int x = 0; x < this.sizeX; ++x) {
        final var r = this.pixelRawAtOrdered(x, y, byteOrder, pixelBuffer);
        segmentBuffer.put(pixelBuffer, 0, r);
      }
    }
  }
}
