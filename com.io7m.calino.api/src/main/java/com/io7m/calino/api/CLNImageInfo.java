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

package com.io7m.calino.api;

import java.util.Objects;
import java.util.Set;

import static com.io7m.calino.api.CLNCompressionMethodStandard.UNCOMPRESSED;

/**
 * Information about an image.
 *
 * This describes the size and format of image data included in a texture file.
 *
 * @param sizeX                  The size, in pixels, of the image data on the X
 *                               axis
 * @param sizeY                  The size, in pixels, of the image data on the Y
 *                               axis
 * @param sizeZ                  The size, in pixels, of the image data on the Z
 *                               axis
 * @param channelsLayout         The layout of the channels in the image data
 * @param channelsType           The type of the channels in the image data
 * @param compressionMethod      The compression method used for the image data
 * @param superCompressionMethod The supercompression method used to encapsulate
 *                               image data
 * @param coordinateSystem       The coordinate system orientation
 * @param colorSpace             The image color space
 * @param flags                  The image flags
 * @param dataByteOrder          The byte order of image data
 */

public record CLNImageInfo(
  int sizeX,
  int sizeY,
  int sizeZ,
  CLNChannelsLayoutDescriptionType channelsLayout,
  CLNChannelsTypeDescriptionType channelsType,
  CLNCompressionMethodType compressionMethod,
  CLNSuperCompressionMethodType superCompressionMethod,
  CLNCoordinateSystem coordinateSystem,
  CLNColorSpaceType colorSpace,
  Set<CLNImageFlagType> flags,
  CLNByteOrder dataByteOrder)
{
  /**
   * Information about an image.
   *
   * This describes the size and format of image data included in a texture
   * file.
   *
   * @param sizeX                  The size, in pixels, of the image data on the
   *                               X axis
   * @param sizeY                  The size, in pixels, of the image data on the
   *                               Y axis
   * @param sizeZ                  The size, in pixels, of the image data on the
   *                               Z axis
   * @param channelsLayout         The layout of the channels in the image data
   * @param channelsType           The type of the channels in the image data
   * @param compressionMethod      The compression method used for the image
   *                               data
   * @param superCompressionMethod The supercompression method used to
   *                               encapsulate image data
   * @param coordinateSystem       The coordinate system orientation
   * @param colorSpace             The image color space
   * @param flags                  The image flags
   * @param dataByteOrder          The byte order of image data
   */

  public CLNImageInfo
  {
    Objects.requireNonNull(channelsLayout, "channelsLayout");
    Objects.requireNonNull(channelsType, "channelsType");
    Objects.requireNonNull(compressionMethod, "compressionMethod");
    Objects.requireNonNull(superCompressionMethod, "superCompressionMethod");
    Objects.requireNonNull(coordinateSystem, "coordinateSystem");
    Objects.requireNonNull(colorSpace, "colorSpace");
    Objects.requireNonNull(flags, "flags");
    Objects.requireNonNull(dataByteOrder, "dataByteOrder");

    if (channelsLayout.bitsTotal() == 0) {
      throw new IllegalArgumentException("Channel layout bits must be > 0");
    }
    if (Integer.compareUnsigned(sizeX, 1) < 0) {
      throw new IllegalArgumentException("SizeX must be >= 1");
    }
    if (Integer.compareUnsigned(sizeY, 1) < 0) {
      throw new IllegalArgumentException("SizeY must be >= 1");
    }
    if (Integer.compareUnsigned(sizeZ, 1) < 0) {
      throw new IllegalArgumentException("SizeZ must be >= 1");
    }
  }

  /**
   * @return The required alignment of texel data
   */

  public int texelBlockAlignment()
  {
    if (this.compressionMethod == UNCOMPRESSED) {
      return this.channelsLayout.texelBlockAlignment();
    }
    return this.compressionMethod.blockAlignment();
  }

  /**
   * @return A humanly-readable description of the image size
   */

  public String showSize()
  {
    return String.format("%d×%d×%d", this.sizeX, this.sizeY, this.sizeZ);
  }
}
