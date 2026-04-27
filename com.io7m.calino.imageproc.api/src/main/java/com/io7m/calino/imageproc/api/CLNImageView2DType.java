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

package com.io7m.calino.imageproc.api;

import com.io7m.calino.api.CLNByteOrder;

import java.lang.foreign.MemorySegment;

/**
 * <p>A view of a mipmap within an image.</p>
 *
 * <p>An image view presents the illusion that a given image comprises pixels with
 * double-precision floating point channels.</p>
 */

public interface CLNImageView2DType
{
  /**
   * Copy this image data to the given memory segment.
   *
   * @param segment   The memory segment
   * @param byteOrder The byte order to which to transform the data
   */

  void copyTo(
    MemorySegment segment,
    CLNByteOrder byteOrder
  );

  /**
   * @return The size of the view on the X axis
   */

  int sizeX();

  /**
   * @return The size of the view on the Y axis
   */

  int sizeY();

  /**
   * Sample a pixel at the given location.
   *
   * @param x     The x location
   * @param y     The y location
   * @param pixel The output pixel
   */

  void pixelAt(
    int x,
    int y,
    double[] pixel);

  /**
   * Sample the raw data of the pixel at the given location. The returned bytes
   * are in the byte order declared in the image file, with no reordering or
   * any reinterpretation.
   *
   * @param x The x location
   * @param y The y location
   *
   * @return The data for one pixel
   */

  byte[] pixelRawAt(
    int x,
    int y);

  /**
   * Sample the raw data of the pixel at the given location. The returned bytes
   * are flipped (if necessary) to match the given byte order.
   *
   * @param x     The x location
   * @param y     The y location
   * @param order The target byte order
   *
   * @return The data for one pixel
   */

  byte[] pixelRawAtOrdered(
    int x,
    int y,
    CLNByteOrder order);

  /**
   * Sample the raw data of the pixel at the given location. The returned bytes
   * are in the byte order declared in the image file, with no reordering or
   * any reinterpretation.
   *
   * @param x      The x location
   * @param y      The y location
   * @param output The output buffer
   *
   * @return The number of bytes written
   */

  int pixelRawAt(
    int x,
    int y,
    byte[] output);

  /**
   * Sample the raw data of the pixel at the given location. The returned bytes
   * are flipped (if necessary) to match the given byte order.
   *
   * @param x      The x location
   * @param y      The y location
   * @param order  The target byte order
   * @param output The output buffer
   *
   * @return The number of bytes written
   */

  int pixelRawAtOrdered(
    int x,
    int y,
    CLNByteOrder order,
    byte[] output);
}
