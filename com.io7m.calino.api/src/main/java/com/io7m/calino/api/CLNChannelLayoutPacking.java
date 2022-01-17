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

import java.text.ParseException;
import java.util.Objects;

/**
 * The available texture packing values.
 */

public enum CLNChannelLayoutPacking implements CLNDescribableType
{
  /**
   * Texture components are packed into an 8-bit value.
   */

  PACK_8 {
    @Override
    public int bitCount()
    {
      return 8;
    }

    @Override
    public String descriptor()
    {
      return "p8";
    }
  },

  /**
   * Texture components are packed into a 16-bit value.
   */

  PACK_16 {
    @Override
    public int bitCount()
    {
      return 16;
    }

    @Override
    public String descriptor()
    {
      return "p16";
    }
  },

  /**
   * Texture components are packed into a 32-bit value.
   */

  PACK_32 {
    @Override
    public int bitCount()
    {
      return 32;
    }

    @Override
    public String descriptor()
    {
      return "p32";
    }
  },

  /**
   * Texture components are packed into a 64-bit value.
   */

  PACK_64 {
    @Override
    public int bitCount()
    {
      return 64;
    }

    @Override
    public String descriptor()
    {
      return "p64";
    }
  };

  /**
   * @return The bit count
   */

  public abstract int bitCount();

  /**
   * Parse a packing value.
   *
   * @param text The text
   *
   * @return A packing value
   *
   * @throws ParseException On errors
   */

  public static CLNChannelLayoutPacking parse(
    final String text)
    throws ParseException
  {
    Objects.requireNonNull(text, "text");

    for (final var known : values()) {
      if (Objects.equals(text, known.descriptor())) {
        return known;
      }
    }

    throw new ParseException(
      String.format("Unrecognized packing value: %s", text),
      0
    );
  }
}
