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

import com.io7m.calino.api.CLNCompressionMethodStandard;
import com.io7m.calino.api.CLNCoordinateSystem;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.imageview.CLNImageViews;
import com.io7m.calino.tests.CLNTestDirectories;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Set;

import static com.io7m.calino.api.CLNByteOrder.BIG_ENDIAN;
import static com.io7m.calino.api.CLNByteOrder.LITTLE_ENDIAN;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R5_G6_B5;
import static com.io7m.calino.api.CLNChannelsTypeDescriptionStandard.FIXED_POINT_NORMALIZED_UNSIGNED;
import static com.io7m.calino.api.CLNColorSpaceStandard.COLOR_SPACE_LINEAR;
import static com.io7m.calino.api.CLNCoordinateAxisR.AXIS_R_INCREASING_AWAY;
import static com.io7m.calino.api.CLNCoordinateAxisS.AXIS_S_INCREASING_RIGHT;
import static com.io7m.calino.api.CLNCoordinateAxisT.AXIS_T_INCREASING_DOWN;
import static com.io7m.calino.tests.CLNTestDirectories.resourceBytesOf;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * @see "CLNGenerateByteArrays565"
 */

public final class CLNImageViewsRawU565Test
{
  private static final CLNCoordinateSystem COORDINATE_SYSTEM =
    new CLNCoordinateSystem(
      AXIS_R_INCREASING_AWAY,
      AXIS_S_INCREASING_RIGHT,
      AXIS_T_INCREASING_DOWN
    );
  private CLNImageViews views;

  @BeforeEach
  public void testSetup()
  {
    this.views =
      new CLNImageViews();
  }

  @Test
  public void testR565_BE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var pixelSize = 2;
    final var order = BIG_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_565_BE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R5_G6_B5,
          FIXED_POINT_NORMALIZED_UNSIGNED,
          CLNCompressionMethodStandard.UNCOMPRESSED,
          CLNSuperCompressionMethodStandard.UNCOMPRESSED,
          COORDINATE_SYSTEM,
          COLOR_SPACE_LINEAR,
          Set.of(),
          order
        ),
        new CLNImage2DDescription(
          0,
          0L,
          data.length,
          0L,
          0
        ),
        data
      );

    for (var y = 0; y < height; ++y) {
      for (var x = 0; x < width; ++x) {
        final var k = view.pixelRawAt(x, y);
        assertEquals(pixelSize, k.length);

        final var px = (k[0] & 0b11111000) >>> 3;
        final var py = ((k[0] & 0b00000111) << 3) | ((k[1] & 0b11100000) >>> 5);
        final var pc = (k[1] & 0b11111);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR565_LE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var pixelSize = 2;
    final var order = LITTLE_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_565_LE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R5_G6_B5,
          FIXED_POINT_NORMALIZED_UNSIGNED,
          CLNCompressionMethodStandard.UNCOMPRESSED,
          CLNSuperCompressionMethodStandard.UNCOMPRESSED,
          COORDINATE_SYSTEM,
          COLOR_SPACE_LINEAR,
          Set.of(),
          order
        ),
        new CLNImage2DDescription(
          0,
          0L,
          data.length,
          0L,
          0
        ),
        data
      );

    for (var y = 0; y < height; ++y) {
      for (var x = 0; x < width; ++x) {
        final var k = view.pixelRawAt(x, y);
        assertEquals(pixelSize, k.length);

        final var px = (k[1] & 0b11111000) >>> 3;
        final var py = ((k[1] & 0b00000111) << 3) | ((k[0] & 0b11100000) >>> 5);
        final var pc = (k[0] & 0b11111);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }
}
