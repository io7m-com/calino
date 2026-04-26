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

import java.nio.ByteBuffer;

abstract class CLNImageView2DRawAbstract32
  extends CLNImageView2DRawAbstract
{
  private final int componentCount;

  protected CLNImageView2DRawAbstract32(
    final CLNImageInfo inImageInfo,
    final int inComponentCount,
    final int mipLevel,
    final byte[] inData)
  {
    super(
      inImageInfo,
      ByteBuffer.wrap(inData),
      mipLevel
    );

    this.componentCount =
      inComponentCount;
  }

  @Override
  public final void pixelRawAtOrdered(
    final int x,
    final int y,
    final CLNByteOrder order,
    final byte[] output)
  {
    final var componentSize = 4;
    final var pixelSize = componentSize * this.componentCount;
    final var lineWidth = this.sizeX() * pixelSize;
    final var pixelData = this.pixelData();

    var outIndex = 0;
    final var base = (y * lineWidth) + (x * pixelSize);
    for (int index = 0; index < this.componentCount; ++index) {
      final var offset = index * componentSize;
      final var c = pixelData.getInt(base + offset);
      switch (order) {
        case BIG_ENDIAN -> {
          output[outIndex + 0] = (byte) ((c >>> 24) & 0xff);
          output[outIndex + 1] = (byte) ((c >>> 16) & 0xff);
          output[outIndex + 2] = (byte) ((c >>> 8) & 0xff);
          output[outIndex + 3] = (byte) ((c >>> 0) & 0xff);
        }
        case LITTLE_ENDIAN -> {
          output[outIndex + 3] = (byte) ((c >>> 24) & 0xff);
          output[outIndex + 2] = (byte) ((c >>> 16) & 0xff);
          output[outIndex + 1] = (byte) ((c >>> 8) & 0xff);
          output[outIndex + 0] = (byte) ((c >>> 0) & 0xff);
        }
      }
      outIndex += componentSize;
    }
  }

  protected final int componentCount()
  {
    return this.componentCount;
  }

  @Override
  public final byte[] pixelRawAtOrdered(
    final int x,
    final int y,
    final CLNByteOrder order)
  {
    final var componentSize = 4;
    final var pixelSize = componentSize * this.componentCount;
    final var out = new byte[pixelSize];
    this.pixelRawAtOrdered(x, y, order, out);
    return out;
  }
}
