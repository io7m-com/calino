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
import com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard;
import com.io7m.calino.api.CLNChannelsTypeDescriptionStandard;
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
import java.lang.foreign.MemorySegment;
import java.nio.file.Path;
import java.util.Set;

import static com.io7m.calino.api.CLNByteOrder.BIG_ENDIAN;
import static com.io7m.calino.api.CLNByteOrder.LITTLE_ENDIAN;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8_A8;
import static com.io7m.calino.api.CLNChannelsTypeDescriptionStandard.FIXED_POINT_NORMALIZED_SIGNED;
import static com.io7m.calino.api.CLNColorSpaceStandard.COLOR_SPACE_LINEAR;
import static com.io7m.calino.api.CLNCoordinateAxisR.AXIS_R_INCREASING_AWAY;
import static com.io7m.calino.api.CLNCoordinateAxisS.AXIS_S_INCREASING_RIGHT;
import static com.io7m.calino.api.CLNCoordinateAxisT.AXIS_T_INCREASING_DOWN;
import static com.io7m.calino.tests.CLNTestDirectories.resourceBytesOf;
import static org.junit.jupiter.api.Assertions.assertArrayEquals;

/**
 * @see "CLNGenerateByteArrays"
 */

public final class CLNImageViewsCopying8Test
{
  private static final int WIDTH = 8;
  private static final int HEIGHT = 8;

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
  public void testR8_FPNS_MemoryCopyLEtoLE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C1_LE.bin",
      "data8x8_S1_C1_LE.bin",
      R8,
      FIXED_POINT_NORMALIZED_SIGNED,
      LITTLE_ENDIAN,
      LITTLE_ENDIAN
    );
  }

  @Test
  public void testR8_FPNS_MemoryCopyLEtoBE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C1_LE.bin",
      "data8x8_S1_C1_BE.bin",
      R8,
      FIXED_POINT_NORMALIZED_SIGNED,
      LITTLE_ENDIAN,
      BIG_ENDIAN
    );
  }

  @Test
  public void testR8_FPNS_MemoryCopyBEtoLE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C1_BE.bin",
      "data8x8_S1_C1_LE.bin",
      R8,
      FIXED_POINT_NORMALIZED_SIGNED,
      BIG_ENDIAN,
      LITTLE_ENDIAN
    );
  }

  @Test
  public void testR8_FPNS_MemoryCopyBEtoBE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C1_BE.bin",
      "data8x8_S1_C1_BE.bin",
      R8,
      FIXED_POINT_NORMALIZED_SIGNED,
      BIG_ENDIAN,
      BIG_ENDIAN
    );
  }

  @Test
  public void testR8G8_FPNS_MemoryCopyLEtoLE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C2_LE.bin",
      "data8x8_S1_C2_LE.bin",
      R8_G8,
      FIXED_POINT_NORMALIZED_SIGNED,
      LITTLE_ENDIAN,
      LITTLE_ENDIAN
    );
  }

  @Test
  public void testR8G8_FPNS_MemoryCopyLEtoBE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C2_LE.bin",
      "data8x8_S1_C2_BE.bin",
      R8_G8,
      FIXED_POINT_NORMALIZED_SIGNED,
      LITTLE_ENDIAN,
      BIG_ENDIAN
    );
  }

  @Test
  public void testR8G8_FPNS_MemoryCopyBEtoLE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C2_BE.bin",
      "data8x8_S1_C2_LE.bin",
      R8_G8,
      FIXED_POINT_NORMALIZED_SIGNED,
      BIG_ENDIAN,
      LITTLE_ENDIAN
    );
  }

  @Test
  public void testR8G8_FPNS_MemoryCopyBEtoBE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C2_BE.bin",
      "data8x8_S1_C2_BE.bin",
      R8_G8,
      FIXED_POINT_NORMALIZED_SIGNED,
      BIG_ENDIAN,
      BIG_ENDIAN
    );
  }

  @Test
  public void testR8G8B8_FPNS_MemoryCopyLEtoLE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C3_LE.bin",
      "data8x8_S1_C3_LE.bin",
      R8_G8_B8,
      FIXED_POINT_NORMALIZED_SIGNED,
      LITTLE_ENDIAN,
      LITTLE_ENDIAN
    );
  }

  @Test
  public void testR8G8B8_FPNS_MemoryCopyLEtoBE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C3_LE.bin",
      "data8x8_S1_C3_BE.bin",
      R8_G8_B8,
      FIXED_POINT_NORMALIZED_SIGNED,
      LITTLE_ENDIAN,
      BIG_ENDIAN
    );
  }

  @Test
  public void testR8G8B8_FPNS_MemoryCopyBEtoLE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C3_BE.bin",
      "data8x8_S1_C3_LE.bin",
      R8_G8_B8,
      FIXED_POINT_NORMALIZED_SIGNED,
      BIG_ENDIAN,
      LITTLE_ENDIAN
    );
  }

  @Test
  public void testR8G8B8_FPNS_MemoryCopyBEtoBE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C3_BE.bin",
      "data8x8_S1_C3_BE.bin",
      R8_G8_B8,
      FIXED_POINT_NORMALIZED_SIGNED,
      BIG_ENDIAN,
      BIG_ENDIAN
    );
  }

  @Test
  public void testR8G8B8A8_FPNS_MemoryCopyLEtoLE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C4_LE.bin",
      "data8x8_S1_C4_LE.bin",
      R8_G8_B8_A8,
      FIXED_POINT_NORMALIZED_SIGNED,
      LITTLE_ENDIAN,
      LITTLE_ENDIAN
    );
  }

  @Test
  public void testR8G8B8A8_FPNS_MemoryCopyLEtoBE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C4_LE.bin",
      "data8x8_S1_C4_BE.bin",
      R8_G8_B8_A8,
      FIXED_POINT_NORMALIZED_SIGNED,
      LITTLE_ENDIAN,
      BIG_ENDIAN
    );
  }

  @Test
  public void testR8G8B8A8_FPNS_MemoryCopyBEtoLE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C4_BE.bin",
      "data8x8_S1_C4_LE.bin",
      R8_G8_B8_A8,
      FIXED_POINT_NORMALIZED_SIGNED,
      BIG_ENDIAN,
      LITTLE_ENDIAN
    );
  }

  @Test
  public void testR8G8B8A8_FPNS_MemoryCopyBEtoBE(
    final @TempDir Path directory)
    throws Exception
  {
    this.runCopy(
      directory,
      "data8x8_S1_C4_BE.bin",
      "data8x8_S1_C4_BE.bin",
      R8_G8_B8_A8,
      FIXED_POINT_NORMALIZED_SIGNED,
      BIG_ENDIAN,
      BIG_ENDIAN
    );
  }

  private void runCopy(
    final Path directory,
    final String dataSourceName,
    final String dataTargetName,
    final CLNChannelsLayoutDescriptionStandard layout,
    final CLNChannelsTypeDescriptionStandard type,
    final CLNByteOrder endianSource,
    final CLNByteOrder endianTarget)
    throws IOException
  {
    final var dataInput =
      resourceBytesOf(CLNTestDirectories.class, directory, dataSourceName);
    final var dataExpected =
      resourceBytesOf(CLNTestDirectories.class, directory, dataTargetName);
    final var dataOutput =
      new byte[dataInput.length];

    final var view =
      this.views.createImageView2D(
        new CLNImageInfo(
          WIDTH,
          HEIGHT,
          1,
          layout,
          type,
          CLNCompressionMethodStandard.UNCOMPRESSED,
          CLNSuperCompressionMethodStandard.UNCOMPRESSED,
          COORDINATE_SYSTEM,
          COLOR_SPACE_LINEAR,
          Set.of(),
          endianSource
        ),
        new CLNImage2DDescription(
          0,
          0L,
          dataInput.length,
          0L,
          0
        ),
        dataInput
      );

    final var segmentOutput = MemorySegment.ofArray(dataOutput);
    view.copyTo(segmentOutput, endianTarget);
    assertArrayEquals(dataExpected, dataOutput);
  }
}
