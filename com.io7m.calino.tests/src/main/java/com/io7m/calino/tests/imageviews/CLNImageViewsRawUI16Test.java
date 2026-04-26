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
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.file.Path;
import java.util.Set;

import static com.io7m.calino.api.CLNByteOrder.BIG_ENDIAN;
import static com.io7m.calino.api.CLNByteOrder.LITTLE_ENDIAN;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R16;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R16_G16;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R16_G16_B16;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R16_G16_B16_A16;
import static com.io7m.calino.api.CLNChannelsTypeDescriptionStandard.INTEGER_UNSIGNED;
import static com.io7m.calino.api.CLNColorSpaceStandard.COLOR_SPACE_LINEAR;
import static com.io7m.calino.api.CLNCoordinateAxisR.AXIS_R_INCREASING_AWAY;
import static com.io7m.calino.api.CLNCoordinateAxisS.AXIS_S_INCREASING_RIGHT;
import static com.io7m.calino.api.CLNCoordinateAxisT.AXIS_T_INCREASING_DOWN;
import static com.io7m.calino.tests.CLNTestDirectories.resourceBytesOf;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * @see "CLNGenerateByteArrays"
 */

public final class CLNImageViewsRawUI16Test
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
    final var componentSize = 2;
    final var pixelSize = components * componentSize;
    final var order = BIG_ENDIAN;
    final var pixel = new double[components];

    final var data = new byte[pixelSize * width * height];
    final var dataBuf = ByteBuffer.wrap(data);
    dataBuf.order(ByteOrder.BIG_ENDIAN);
    dataBuf.putShort(0, (short) 0);
    dataBuf.putShort(2, (short) 0x7fff);
    dataBuf.putShort(4, (short) 0xffff);

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16,
          INTEGER_UNSIGNED,
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
    final var componentSize = 2;
    final var pixelSize = components * componentSize;
    final var order = LITTLE_ENDIAN;
    final var pixel = new double[components];

    final var data = new byte[pixelSize * width * height];
    final var dataBuf = ByteBuffer.wrap(data);
    dataBuf.order(ByteOrder.LITTLE_ENDIAN);
    dataBuf.putShort(0, (short) 0);
    dataBuf.putShort(2, (short) 0x7fff);
    dataBuf.putShort(4, (short) 0xffff);

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16,
          INTEGER_UNSIGNED,
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
  public void testR16_BE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 1;
    final var componentSize = 2;
    final var order = BIG_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S2_C1_BE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16,
          INTEGER_UNSIGNED,
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
        assertEquals(components * componentSize, k.length);

        final var px = (k[0] >>> 4) & 0b1111;
        final var py = (k[0] >>> 0) & 0b1111;
        final var pc = (k[1] & 0b1111);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR16_LE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 1;
    final var componentSize = 2;
    final var order = LITTLE_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S2_C1_LE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16,
          INTEGER_UNSIGNED,
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
        assertEquals(components * componentSize, k.length);

        final var px = (k[1] >>> 4) & 0b1111;
        final var py = (k[1] >>> 0) & 0b1111;
        final var pc = (k[0] & 0b1111);

        assertEquals(x, px);
        assertEquals(y, py);
        assertEquals(0, pc);
      }
    }
  }

  @Test
  public void testR16G16_BE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 2;
    final var componentSize = 2;
    final var order = BIG_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S2_C2_BE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16_G16,
          INTEGER_UNSIGNED,
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
        assertEquals(components * componentSize, k.length);

        final var px0 = (k[0] >>> 4) & 0b1111;
        final var py0 = (k[0] >>> 0) & 0b1111;
        final var pc0 = (k[1] & 0b1111);
        final var px1 = (k[2] >>> 4) & 0b1111;
        final var py1 = (k[2] >>> 0) & 0b1111;
        final var pc1 = (k[3] & 0b1111);

        assertEquals(x, px0);
        assertEquals(x, px1);
        assertEquals(y, py0);
        assertEquals(y, py1);
        assertEquals(0, pc0);
        assertEquals(1, pc1);
      }
    }
  }

  @Test
  public void testR16G16_LE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 2;
    final var componentSize = 2;
    final var order = LITTLE_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S2_C2_LE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16_G16,
          INTEGER_UNSIGNED,
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
        assertEquals(components * componentSize, k.length);

        final var px0 = (k[1] >>> 4) & 0b1111;
        final var py0 = (k[1] >>> 0) & 0b1111;
        final var pc0 = (k[0] & 0b1111);
        final var px1 = (k[3] >>> 4) & 0b1111;
        final var py1 = (k[3] >>> 0) & 0b1111;
        final var pc1 = (k[2] & 0b1111);

        assertEquals(x, px0);
        assertEquals(x, px1);
        assertEquals(y, py0);
        assertEquals(y, py1);
        assertEquals(0, pc0);
        assertEquals(1, pc1);
      }
    }
  }

  @Test
  public void testR16G16B16_BE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 3;
    final var componentSize = 2;
    final var order = BIG_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S2_C3_BE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16_G16_B16,
          INTEGER_UNSIGNED,
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
        assertEquals(components * componentSize, k.length);

        final var px0 = (k[0] >>> 4) & 0b1111;
        final var py0 = (k[0] >>> 0) & 0b1111;
        final var pc0 = (k[1] & 0b1111);
        final var px1 = (k[2] >>> 4) & 0b1111;
        final var py1 = (k[2] >>> 0) & 0b1111;
        final var pc1 = (k[3] & 0b1111);
        final var px2 = (k[4] >>> 4) & 0b1111;
        final var py2 = (k[4] >>> 0) & 0b1111;
        final var pc2 = (k[5] & 0b1111);

        assertEquals(x, px0);
        assertEquals(x, px1);
        assertEquals(x, px2);
        assertEquals(y, py0);
        assertEquals(y, py1);
        assertEquals(y, py2);
        assertEquals(0, pc0);
        assertEquals(1, pc1);
        assertEquals(2, pc2);
      }
    }
  }

  @Test
  public void testR16G16B16_LE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 3;
    final var componentSize = 2;
    final var order = LITTLE_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S2_C3_LE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16_G16_B16,
          INTEGER_UNSIGNED,
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
        assertEquals(components * componentSize, k.length);

        final var px0 = (k[1] >>> 4) & 0b1111;
        final var py0 = (k[1] >>> 0) & 0b1111;
        final var pc0 = (k[0] & 0b1111);
        final var px1 = (k[3] >>> 4) & 0b1111;
        final var py1 = (k[3] >>> 0) & 0b1111;
        final var pc1 = (k[2] & 0b1111);
        final var px2 = (k[5] >>> 4) & 0b1111;
        final var py2 = (k[5] >>> 0) & 0b1111;
        final var pc2 = (k[4] & 0b1111);

        assertEquals(x, px0);
        assertEquals(x, px1);
        assertEquals(x, px2);
        assertEquals(y, py0);
        assertEquals(y, py1);
        assertEquals(y, py2);
        assertEquals(0, pc0);
        assertEquals(1, pc1);
        assertEquals(2, pc2);
      }
    }
  }

  @Test
  public void testR16G16B16A16_BE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 4;
    final var componentSize = 2;
    final var order = BIG_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S2_C4_BE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16_G16_B16_A16,
          INTEGER_UNSIGNED,
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
        assertEquals(components * componentSize, k.length);

        final var px0 = (k[0] >>> 4) & 0b1111;
        final var py0 = (k[0] >>> 0) & 0b1111;
        final var pc0 = (k[1] & 0b1111);
        final var px1 = (k[2] >>> 4) & 0b1111;
        final var py1 = (k[2] >>> 0) & 0b1111;
        final var pc1 = (k[3] & 0b1111);
        final var px2 = (k[4] >>> 4) & 0b1111;
        final var py2 = (k[4] >>> 0) & 0b1111;
        final var pc2 = (k[5] & 0b1111);
        final var px3 = (k[6] >>> 4) & 0b1111;
        final var py3 = (k[6] >>> 0) & 0b1111;
        final var pc3 = (k[7] & 0b1111);

        assertEquals(x, px0);
        assertEquals(x, px1);
        assertEquals(x, px2);
        assertEquals(x, px3);
        assertEquals(y, py0);
        assertEquals(y, py1);
        assertEquals(y, py2);
        assertEquals(y, py3);
        assertEquals(0, pc0);
        assertEquals(1, pc1);
        assertEquals(2, pc2);
        assertEquals(3, pc3);
      }
    }
  }

  @Test
  public void testR16G16B16A16_LE(
    final @TempDir Path directory)
    throws IOException
  {
    final var width = 8;
    final var height = 8;
    final var components = 4;
    final var componentSize = 2;
    final var order = LITTLE_ENDIAN;

    final var data =
      resourceBytesOf(
        CLNTestDirectories.class,
        directory,
        "data8x8_S2_C4_LE.bin"
      );

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          width, height, 1,
          R16_G16_B16_A16,
          INTEGER_UNSIGNED,
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
        assertEquals(components * componentSize, k.length);

        final var px0 = (k[1] >>> 4) & 0b1111;
        final var py0 = (k[1] >>> 0) & 0b1111;
        final var pc0 = (k[0] & 0b1111);
        final var px1 = (k[3] >>> 4) & 0b1111;
        final var py1 = (k[3] >>> 0) & 0b1111;
        final var pc1 = (k[2] & 0b1111);
        final var px2 = (k[5] >>> 4) & 0b1111;
        final var py2 = (k[5] >>> 0) & 0b1111;
        final var pc2 = (k[4] & 0b1111);
        final var px3 = (k[7] >>> 4) & 0b1111;
        final var py3 = (k[7] >>> 0) & 0b1111;
        final var pc3 = (k[6] & 0b1111);

        assertEquals(x, px0);
        assertEquals(x, px1);
        assertEquals(x, px2);
        assertEquals(x, px3);
        assertEquals(y, py0);
        assertEquals(y, py1);
        assertEquals(y, py2);
        assertEquals(y, py3);
        assertEquals(0, pc0);
        assertEquals(1, pc1);
        assertEquals(2, pc2);
        assertEquals(3, pc3);
      }
    }
  }
}
