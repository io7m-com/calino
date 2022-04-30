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
import java.nio.channels.WritableByteChannel;

/**
 * The writable mipmaps for a 2D image.
 *
 * Users are expected to retrieve the byte channel associated with each mipmap
 * level using {@link #writeMipMap(int)}, and are expected to write
 * supercompressed data to the byte channel in accordance with the declared
 * image info.
 */

public interface CLWritableMipMaps2DType
{
  /**
   * Retrieve the byte channel associated with a mipmap level.
   *
   * @param mipMapLevel The mipmap level
   *
   * @return A byte channel that must receive supercompressed image data
   *
   * @throws IOException On errors
   */

  WritableByteChannel writeMipMap(int mipMapLevel)
    throws IOException;
}
