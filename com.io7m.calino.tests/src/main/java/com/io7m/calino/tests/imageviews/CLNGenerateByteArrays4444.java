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

package com.io7m.calino.tests.imageviews;

import com.io7m.calino.api.CLNByteOrder;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.file.Files;
import java.nio.file.Paths;

public final class CLNGenerateByteArrays4444
{
  private CLNGenerateByteArrays4444()
  {
  }

  static void main()
    throws IOException
  {
    for (final var order : CLNByteOrder.values()) {
      writeBuffer(order, 8, 8);
    }
  }

  private static void writeBuffer(
    final CLNByteOrder order,
    final int height,
    final int width)
    throws IOException
  {
    final var data =
      new byte[height * (width * 2)];
    final var dataBuffer =
      ByteBuffer.wrap(data);

    switch (order) {
      case BIG_ENDIAN -> {
        dataBuffer.order(ByteOrder.BIG_ENDIAN);
      }
      case LITTLE_ENDIAN -> {
        dataBuffer.order(ByteOrder.LITTLE_ENDIAN);
      }
    }

    for (int y = 0; y < height; ++y) {
      for (int x = 0; x < width; ++x) {
        final var rowLength =
          (width * 2);
        final var offset =
          (y * rowLength) + (x * 2);

        // 0bxxxx_0000_0000_yyyy
        var d = 0;
        d |= ((x & 0b1111) << 12);
        d |= ((y & 0b1111));
        dataBuffer.putChar(offset, (char) d);
      }
    }

    final var name = new StringBuilder();
    name.append("data8x8_4444_");
    name.append(switch (order) {
      case BIG_ENDIAN -> "BE";
      case LITTLE_ENDIAN -> "LE";
    });
    name.append(".bin");

    Files.write(Paths.get(name.toString()), data);
  }
}
