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

public final class CLNGenerateByteArrays
{
  private CLNGenerateByteArrays()
  {
  }

  enum Size
  {
    S1, S2, S4, S8;

    public int size()
    {
      return switch (this) {
        case S1 -> 1;
        case S2 -> 2;
        case S4 -> 4;
        case S8 -> 8;
      };
    };
  }

  static void main()
    throws IOException
  {
    final var width = 8;
    final var height = 8;

    final var componentSizes =
      new Size[]{Size.S1, Size.S2, Size.S4, Size.S8};
    final var componentCounts =
      new int[]{1, 2, 3, 4};

    for (final var componentSize : componentSizes) {
      for (final var componentCount : componentCounts) {
        for (final var order : CLNByteOrder.values()) {
          writeBuffer(componentSize, componentCount, order, height, width);
        }
      }
    }
  }

  private static void writeBuffer(
    final Size componentSize,
    final int componentCount,
    final CLNByteOrder order,
    final int height,
    final int width)
    throws IOException
  {
    final int pixelSize =
      componentSize.size() * componentCount;
    final var data =
      new byte[height * (width * pixelSize)];
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
          (width * pixelSize);
        final var offset =
          (y * rowLength) + (x * pixelSize);

        switch (componentSize) {
          case S1 -> {
            for (int c = 0; c < componentCount; ++c) {
              // 0bxxxyyycc
              var d = 0;
              d |= (x << 5);
              d |= (y << 2);
              d |= c;
              final var cOffset = c * componentSize.size();
              dataBuffer.put(offset + cOffset, (byte) d);
            }
          }
          case S2 -> {
            for (int c = 0; c < componentCount; ++c) {
              // 0bxxxxyyyy_0000cccc
              var d = 0;
              d |= (x << 12);
              d |= (y << 8);
              d |= c;
              final var cOffset = c * componentSize.size();
              dataBuffer.putChar(offset + cOffset, (char) d);
            }
          }
          case S4 -> {
            for (int c = 0; c < componentCount; ++c) {
              // 0bxxxxxxxx_yyyyyyyy_00000000_cccccccc
              var d = 0;
              d |= (x << 24);
              d |= (y << 16);
              d |= c;
              final var cOffset = c * componentSize.size();
              dataBuffer.putInt(offset + cOffset, d);
            }
          }
          case S8 -> {
            for (int c = 0; c < componentCount; ++c) {
              var d = 0L;
              final long xc = (x & 0b11111111L) << 56L;
              final long yc = (y & 0b11111111L) << 48L;
              final long cc = (c & 0b11111111L);
              d |= xc;
              d |= yc;
              d |= cc;
              final var cOffset = c * componentSize.size();
              dataBuffer.putLong(offset + cOffset, d);
            }
          }
        }
      }
    }

    final var name = new StringBuilder();
    name.append("data8x8_");
    name.append(componentSize);
    name.append("_");
    name.append("C");
    name.append(componentCount);
    name.append("_");
    name.append(switch (order) {
      case BIG_ENDIAN -> "BE";
      case LITTLE_ENDIAN -> "LE";
    });
    name.append(".bin");

    Files.write(Paths.get(name.toString()), data);
  }
}
