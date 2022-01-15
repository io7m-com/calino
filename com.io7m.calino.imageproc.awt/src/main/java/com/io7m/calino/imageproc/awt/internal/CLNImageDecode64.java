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

package com.io7m.calino.imageproc.awt.internal;

import java.awt.image.BufferedImage;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.Objects;

public final class CLNImageDecode64 implements CLNImageDecodeType
{
  private final ByteOrder byteOrder;
  private final int targetComponents;
  private final int pixelSizeBytes;

  public CLNImageDecode64(
    final ByteOrder inByteOrder,
    final int inTargetComponents)
  {
    this.byteOrder =
      Objects.requireNonNull(inByteOrder, "byteOrder");
    this.pixelSizeBytes =
      inTargetComponents * 8;
    this.targetComponents =
      inTargetComponents;
  }

  @Override
  public byte[] execute(
    final BufferedImage image)
  {
    final var imageAccess = new CLNImageAccess(image);
    final var pixel = new double[4];
    final var width = image.getWidth();
    final var height = image.getHeight();
    final var data = new byte[(width * this.pixelSizeBytes) * height];
    final var buffer = ByteBuffer.wrap(data);
    buffer.order(this.byteOrder);

    for (int y = 0; y < height; ++y) {
      for (int x = 0; x < width; ++x) {
        pixel[0] = 0.0;
        pixel[1] = 0.0;
        pixel[2] = 0.0;
        pixel[3] = 1.0;
        imageAccess.pixelAt(x, y, pixel);

        for (int c = 0; c < this.targetComponents; ++c) {
          buffer.putLong((long) (pixel[c] * 18446744073709551615.0));
        }
      }
    }

    return data;
  }
}
