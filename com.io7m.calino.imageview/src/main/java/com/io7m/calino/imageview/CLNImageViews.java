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

package com.io7m.calino.imageview;

import com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard;
import com.io7m.calino.api.CLNChannelsTypeDescriptionStandard;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.imageproc.api.CLNImageView2DType;
import com.io7m.calino.imageproc.api.CLNImageViewFactoryType;
import com.io7m.calino.imageview.internal.CLNImageView2DFixedU16;
import com.io7m.calino.imageview.internal.CLNImageView2DFixedU32;
import com.io7m.calino.imageview.internal.CLNImageView2DFixedU4444;
import com.io7m.calino.imageview.internal.CLNImageView2DFixedU565;
import com.io7m.calino.imageview.internal.CLNImageView2DFixedU64;
import com.io7m.calino.imageview.internal.CLNImageView2DFixedU8;

import java.util.Objects;

import static java.lang.Integer.toUnsignedLong;

/**
 * The default factory of image views.
 */

public final class CLNImageViews implements CLNImageViewFactoryType
{
  /**
   * The default factory of image views.
   */

  public CLNImageViews()
  {

  }

  @Override
  public CLNImageView2DType createImageView2D(
    final CLNImageInfo imageInfo,
    final CLNImage2DDescription image2DDescription,
    final byte[] data)
  {
    Objects.requireNonNull(imageInfo, "imageInfo");
    Objects.requireNonNull(image2DDescription, "image2DDescription");
    Objects.requireNonNull(data, "data");

    final var sizeExpected = image2DDescription.dataSizeUncompressed();
    final var sizeReceived = toUnsignedLong(data.length);
    if (sizeReceived != sizeExpected) {
      final var lineSeparator = System.lineSeparator();
      throw new IllegalArgumentException(
        new StringBuilder(128)
          .append("Incorrect data length.")
          .append(lineSeparator)
          .append("  Expected: ")
          .append(Long.toUnsignedString(sizeExpected))
          .append(lineSeparator)
          .append("  Received: ")
          .append(Long.toUnsignedString(sizeReceived))
          .append(lineSeparator)
          .toString()
      );
    }

    final var layout = imageInfo.channelsLayout();
    if (layout instanceof CLNChannelsLayoutDescriptionStandard standard) {
      return createImageView2DStandard(imageInfo, data, standard);
    }

    throw new UnsupportedOperationException(
      new StringBuilder(64)
        .append("Channel layouts of type ")
        .append(layout.descriptor())
        .append(" are not supported")
        .toString()
    );
  }

  private static CLNImageView2DType createImageView2DStandard(
    final CLNImageInfo imageInfo,
    final byte[] data,
    final CLNChannelsLayoutDescriptionStandard standard)
  {
    final var componentCount = standard.channels().size();

    final var type = imageInfo.channelsType();
    if (type instanceof CLNChannelsTypeDescriptionStandard typeStandard) {
      return switch (typeStandard) {
        case FIXED_POINT_NORMALIZED_UNSIGNED -> {
          yield createImageView2DFixedU(
            imageInfo,
            data,
            standard,
            componentCount);
        }
        case FIXED_POINT_NORMALIZED_SIGNED,
          FLOATING_POINT_IEEE754_UNSIGNED,
          FLOATING_POINT_IEEE754_SIGNED,
          INTEGER_SIGNED,
          INTEGER_UNSIGNED,
          SCALED_SIGNED,
          SCALED_UNSIGNED -> {
          throw new UnsupportedOperationException(
            new StringBuilder(64)
              .append("Components of type ")
              .append(typeStandard)
              .append(" are not yet supported")
              .toString()
          );
        }
      };
    }

    throw new UnsupportedOperationException(
      new StringBuilder(64)
        .append("Components of type ")
        .append(type.descriptor())
        .append(" are not supported")
        .toString()
    );
  }

  private static CLNImageView2DType createImageView2DFixedU(
    final CLNImageInfo imageInfo,
    final byte[] data,
    final CLNChannelsLayoutDescriptionStandard standard,
    final int componentCount)
  {
    return switch (standard) {
      case R5_G6_B5 -> {
        yield new CLNImageView2DFixedU565(imageInfo, data);
      }
      case R4_G4_B4_A4 -> {
        yield new CLNImageView2DFixedU4444(imageInfo, data);
      }
      case R8, R8_G8, R8_G8_B8_A8, R8_G8_B8 -> {
        yield new CLNImageView2DFixedU8(imageInfo, data, componentCount);
      }
      case R16, R16_G16_B16_A16, R16_G16_B16, R16_G16 -> {
        yield new CLNImageView2DFixedU16(imageInfo, data, componentCount);
      }
      case R32, R32_G32_B32_A32, R32_G32_B32, R32_G32 -> {
        yield new CLNImageView2DFixedU32(imageInfo, data, componentCount);
      }
      case R64, R64_G64_B64_A64, R64_G64_B64, R64_G64 -> {
        yield new CLNImageView2DFixedU64(imageInfo, data, componentCount);
      }
    };
  }
}
