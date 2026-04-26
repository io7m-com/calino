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
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8_A8;
import static com.io7m.calino.api.CLNChannelsTypeDescriptionStandard.FIXED_POINT_NORMALIZED_UNSIGNED;
import static com.io7m.calino.api.CLNColorSpaceStandard.COLOR_SPACE_LINEAR;
import static com.io7m.calino.api.CLNCoordinateAxisR.AXIS_R_INCREASING_AWAY;
import static com.io7m.calino.api.CLNCoordinateAxisS.AXIS_S_INCREASING_RIGHT;
import static com.io7m.calino.api.CLNCoordinateAxisT.AXIS_T_INCREASING_DOWN;
import static com.io7m.calino.tests.CLNTestDirectories.resourceBytesOf;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * @see "CLNGenerateByteArrays"
 */

public final class CLNImageViewsRawU8Test
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
  public void testPixel_BE()
  {
    final var width = 3;
    final var height = 1;
    final var components = 1;
    final var componentSize = 1;
    final var pixelSize = components * componentSize;
    final var order = BIG_ENDIAN;
    final var pixel = new double[components];

    final var data = new byte[pixelSize * width * height];
    data[0] = (byte) 0;
    data[1] = (byte) 0x7f;
    data[2] = (byte) 0xff;

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8,
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

    view.pixelAt(0, 0, pixel);
    assertEquals(0.0, pixel[0], 0.01);
    view.pixelAt(1, 0, pixel);
    assertEquals(0.5, pixel[0], 0.01);
    view.pixelAt(2, 0, pixel);
    assertEquals(1.0, pixel[0], 0.01);
  }

  @Test
  public void testPixel_LE()
  {
    final var width = 3;
    final var height = 1;
    final var components = 1;
    final var componentSize = 1;
    final var pixelSize = components * componentSize;
    final var order = LITTLE_ENDIAN;
    final var pixel = new double[components];

    final var data = new byte[pixelSize * width * height];
    data[0] = (byte) 0;
    data[1] = (byte) 0x7f;
    data[2] = (byte) 0xff;

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8,
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

    view.pixelAt(0, 0, pixel);
    assertEquals(0.0, pixel[0], 0.01);
    view.pixelAt(1, 0, pixel);
    assertEquals(0.5, pixel[0], 0.01);
    view.pixelAt(2, 0, pixel);
    assertEquals(1.0, pixel[0], 0.01);
  }

  @Test
  public void testR8_BE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 1;
    final var order = BIG_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S1_C1_BE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8,
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
        assertEquals(components, k.length);

        final var px = (k[0] >>> 5) & 0b111;
        final var py = (k[0] >>> 2) & 0b111;
        final var pc = (k[0] & 0b11);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR8_LE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 1;
    final var order = LITTLE_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S1_C1_LE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8,
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
        assertEquals(components, k.length);

        final var px = (k[0] >>> 5) & 0b111;
        final var py = (k[0] >>> 2) & 0b111;
        final var pc = (k[0] & 0b11);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR8G8_BE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 2;
    final var order = BIG_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S1_C2_BE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8_G8,
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
        assertEquals(components, k.length);

        final var px = (k[0] >>> 5) & 0b111;
        final var py = (k[0] >>> 2) & 0b111;
        final var pc = (k[0] & 0b11);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR8G8_LE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 2;
    final var order = LITTLE_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S1_C2_LE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8_G8,
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
        assertEquals(components, k.length);

        final var px = (k[0] >>> 5) & 0b111;
        final var py = (k[0] >>> 2) & 0b111;
        final var pc = (k[0] & 0b11);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR8G8B8_BE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 3;
    final var order = BIG_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S1_C3_BE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8_G8_B8,
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
        assertEquals(components, k.length);

        final var px = (k[0] >>> 5) & 0b111;
        final var py = (k[0] >>> 2) & 0b111;
        final var pc = (k[0] & 0b11);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR8G8B8_LE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 3;
    final var order = LITTLE_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S1_C3_LE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8_G8_B8,
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
        assertEquals(components, k.length);

        final var px = (k[0] >>> 5) & 0b111;
        final var py = (k[0] >>> 2) & 0b111;
        final var pc = (k[0] & 0b11);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR8G8B8A8_BE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 4;
    final var order = BIG_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S1_C4_BE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8_G8_B8_A8,
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
        assertEquals(components, k.length);

        final var px = (k[0] >>> 5) & 0b111;
        final var py = (k[0] >>> 2) & 0b111;
        final var pc = (k[0] & 0b11);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR8G8B8A8_LE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 4;
    final var order = LITTLE_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S1_C4_LE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R8_G8_B8_A8,
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
        assertEquals(components, k.length);

        final var px = (k[0] >>> 5) & 0b111;
        final var py = (k[0] >>> 2) & 0b111;
        final var pc = (k[0] & 0b11);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }
}
