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

/**
 * An RGB565 decoder.
 */

public final class CLNImageDecodeR5G6B5 implements CLNImageDecodeType
{
  private final ByteOrder order;

  /**
   * An RGB565 decoder.
   *
   * @param inOrder The byte order
   */

  public CLNImageDecodeR5G6B5(
    final ByteOrder inOrder)
  {
    this.order = Objects.requireNonNull(inOrder, "order");
  }

  @Override
  public byte[] execute(
    final BufferedImage image)
  {
    final var width = image.getWidth();
    final var height = image.getHeight();
    final var data = new byte[(width * 2) * height];
    final var buffer = ByteBuffer.wrap(data);
    buffer.order(this.order);

    for (int y = 0; y < height; ++y) {
      for (int x = 0; x < width; ++x) {
        final var argb = image.getRGB(x, y);
        final var r = (argb >> 16) & 0xff;
        final var g = (argb >> 8) & 0xff;
        final var b = argb & 0xff;

        final var dr = (double) r / 255.0;
        final var dg = (double) g / 255.0;
        final var db = (double) b / 255.0;

        final var r5 = dr * 31.0;
        final var g6 = dg * 63.0;
        final var b5 = db * 31.0;

        final int sr = (short) ((int) r5 << 11);
        final int sg = (short) ((int) g6 << 5);
        final int sb = (short) b5;

        final short result = (short) ((sr | sg | sb) & 0xffff);
        buffer.putShort(result);
      }
    }

    return data;
  }
}
