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

package com.io7m.calino.tests;

import com.io7m.calino.api.CLNChannelDescription;
import com.io7m.calino.api.CLNChannelSemantic;
import com.io7m.calino.api.CLNChannelsLayoutDescriptionCustom;
import com.io7m.calino.api.CLNChannelsTypeDescriptionCustom;
import com.io7m.calino.api.CLNChannelsTypeDescriptionStandard;
import com.io7m.calino.api.CLNChannelsTypeDescriptionType;
import com.io7m.calino.api.CLNCompressionMethodStandard;
import com.io7m.calino.api.CLNCoordinateSystem;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.imageview.CLNImageViews;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

import static com.io7m.calino.api.CLNByteOrder.LITTLE_ENDIAN;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8;
import static com.io7m.calino.api.CLNChannelsTypeDescriptionStandard.FIXED_POINT_NORMALIZED_UNSIGNED;
import static com.io7m.calino.api.CLNColorSpaceStandard.COLOR_SPACE_SRGB;
import static com.io7m.calino.api.CLNCoordinateAxisR.AXIS_R_INCREASING_TOWARD;
import static com.io7m.calino.api.CLNCoordinateAxisS.AXIS_S_INCREASING_RIGHT;
import static com.io7m.calino.api.CLNCoordinateAxisT.AXIS_T_INCREASING_DOWN;
import static org.junit.jupiter.api.Assertions.assertThrows;

public final class CLNImageViewsTest
{
  @TestFactory
  public Stream<DynamicTest> testUnsupportedTypeCases()
  {
    final var standardUnsupported =
      Stream.of(CLNChannelsTypeDescriptionStandard.values())
        .filter(s -> s != FIXED_POINT_NORMALIZED_UNSIGNED);

    final var customUnsupported =
      Stream.of(new CLNChannelsTypeDescriptionCustom("WEIRD"));

    return Stream.concat(standardUnsupported, customUnsupported)
      .map(CLNImageViewsTest::unsupportedTypeCase);
  }

  @Test
  public void testUnsupportedChannelLayout()
  {
    final var imageViews = new CLNImageViews();

    final var imageInfo =
      new CLNImageInfo(
        32,
        32,
        1,
        new CLNChannelsLayoutDescriptionCustom(List.of(
          new CLNChannelDescription(CLNChannelSemantic.STENCIL, 128)
        ), Optional.empty()),
        FIXED_POINT_NORMALIZED_UNSIGNED,
        CLNCompressionMethodStandard.UNCOMPRESSED,
        CLNSuperCompressionMethodStandard.UNCOMPRESSED,
        new CLNCoordinateSystem(
          AXIS_R_INCREASING_TOWARD,
          AXIS_S_INCREASING_RIGHT,
          AXIS_T_INCREASING_DOWN),
        COLOR_SPACE_SRGB,
        Set.of(),
        LITTLE_ENDIAN
      );

    final var imageDescription =
      new CLNImage2DDescription(
        0,
        0L,
        3L,
        3L,
        0
      );

    assertThrows(UnsupportedOperationException.class, () -> {
      imageViews.createImageView2D(
        imageInfo,
        imageDescription,
        new byte[3]
      );
    });
  }

  @Test
  public void testIncorrectDataLength()
  {
    final var imageViews = new CLNImageViews();

    final var imageInfo =
      new CLNImageInfo(
        32,
        32,
        1,
        new CLNChannelsLayoutDescriptionCustom(List.of(
          new CLNChannelDescription(CLNChannelSemantic.STENCIL, 128)
        ), Optional.empty()),
        FIXED_POINT_NORMALIZED_UNSIGNED,
        CLNCompressionMethodStandard.UNCOMPRESSED,
        CLNSuperCompressionMethodStandard.UNCOMPRESSED,
        new CLNCoordinateSystem(
          AXIS_R_INCREASING_TOWARD,
          AXIS_S_INCREASING_RIGHT,
          AXIS_T_INCREASING_DOWN),
        COLOR_SPACE_SRGB,
        Set.of(),
        LITTLE_ENDIAN
      );

    final var imageDescription =
      new CLNImage2DDescription(
        0,
        0L,
        1024L,
        1024L,
        0
      );

    assertThrows(IllegalArgumentException.class, () -> {
      imageViews.createImageView2D(
        imageInfo,
        imageDescription,
        new byte[3]
      );
    });
  }

  private static DynamicTest unsupportedTypeCase(
    final CLNChannelsTypeDescriptionType s)
  {
    final var imageViews = new CLNImageViews();

    return DynamicTest.dynamicTest(
      String.format("testUnsupportedTypeCase|%s", s),
      () -> {
        final var imageInfo =
          new CLNImageInfo(
            32,
            32,
            1,
            R8_G8_B8,
            s,
            CLNCompressionMethodStandard.UNCOMPRESSED,
            CLNSuperCompressionMethodStandard.UNCOMPRESSED,
            new CLNCoordinateSystem(
              AXIS_R_INCREASING_TOWARD,
              AXIS_S_INCREASING_RIGHT,
              AXIS_T_INCREASING_DOWN),
            COLOR_SPACE_SRGB,
            Set.of(),
            LITTLE_ENDIAN
          );

        final var imageDescription =
          new CLNImage2DDescription(
            0,
            0L,
            3L,
            3L,
            0
          );

        assertThrows(UnsupportedOperationException.class, () -> {
          imageViews.createImageView2D(
            imageInfo,
            imageDescription,
            new byte[3]
          );
        });
      }
    );
  }
}
