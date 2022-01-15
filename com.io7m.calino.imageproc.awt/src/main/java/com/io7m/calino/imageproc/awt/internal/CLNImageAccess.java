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

package com.io7m.calino.imageproc.awt.internal;

import java.awt.image.BufferedImage;
import java.awt.image.WritableRaster;
import java.util.Objects;

/**
 * Normalized access to a buffered image.
 */

public final class CLNImageAccess
{
  private final BufferedImage image;
  private final double[] scales;
  private final WritableRaster raster;

  CLNImageAccess(
    final BufferedImage inImage)
  {
    this.image =
      Objects.requireNonNull(inImage, "image");
    this.raster =
      this.image.getRaster();

    final var sizes =
      this.image.getColorModel().getComponentSize();

    this.scales = new double[sizes.length];
    for (int index = 0; index < sizes.length; ++index) {
      this.scales[index] = (1 << sizes[index]) - 1;
    }
  }

  /**
   * Get the pixel at {@code (x,y)}, normalizing the values to [0.0, 1.0].
   *
   * @param x      The x position
   * @param y      The y position
   * @param sample The output sample
   */

  public void pixelAt(
    final int x,
    final int y,
    final double[] sample)
  {
    this.raster.getPixel(x, y, sample);
    for (int index = 0; index < this.scales.length; ++index) {
      sample[index] /= this.scales[index];
    }
  }
}
