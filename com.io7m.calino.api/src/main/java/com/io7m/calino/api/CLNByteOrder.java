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

/**
 * The endianness/byte order for the components of image data that are larger
 * than a single byte.
 */

public enum CLNByteOrder implements CLNDescribableType
{
  /**
   * The most significant byte appears first.
   */

  BIG_ENDIAN {
    @Override
    public String descriptor()
    {
      return "BIG_ENDIAN";
    }
  },

  /**
   * The most significant byte appears last.
   */

  LITTLE_ENDIAN {
    @Override
    public String descriptor()
    {
      return "LITTLE_ENDIAN";
    }
  }
}
