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

import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNImageInfo;

/**
 * A factory of image views.
 */

public interface CLNImageViewFactoryType
{
  /**
   * Create a new view of the given data.
   *
   * @param imageInfo          The image info
   * @param image2DDescription The particular 2D image description
   * @param data               The raw image bytes
   *
   * @return A new image view
   */

  CLNImageView2DType createImageView2D(
    CLNImageInfo imageInfo,
    CLNImage2DDescription image2DDescription,
    byte[] data
  );

  /**
   * Create a new view of the given data.
   *
   * @param imageInfo             The image info
   * @param imageArrayDescription The particular array image description
   * @param data                  The raw image bytes
   *
   * @return A new image view
   */

  CLNImageView2DType createImageViewArray(
    CLNImageInfo imageInfo,
    CLNImageArrayDescription imageArrayDescription,
    byte[] data
  );
}
