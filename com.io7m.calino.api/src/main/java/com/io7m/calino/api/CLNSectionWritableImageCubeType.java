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

import java.io.IOException;

/**
 * A writable cube image section.
 */

public non-sealed interface CLNSectionWritableImageCubeType
  extends CLNSectionWritableStandardType
{
  /**
   * Create a set of mipmaps in the image.
   *
   * @param mipMaps The mipmap descriptions
   *
   * @return An interface used to write mipmap data
   *
   * @throws IOException On errors
   */

  CLWritableMipMapsCubeType createMipMaps(
    CLNImageCubeMipMapDeclarations mipMaps)
    throws IOException;
}
