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
 * The standard channel types.
 */

public enum CLNChannelsTypeDescriptionStandard
  implements CLNChannelsTypeDescriptionType
{
  /**
   * The channel consists of unsigned, normalized, fixed-point values.
   */

  FIXED_POINT_NORMALIZED_UNSIGNED {
    @Override
    public String descriptor()
    {
      return "FIXED_POINT_NORMALIZED_UNSIGNED";
    }
  },

  /**
   * The channel consists of signed, normalized, fixed-point values.
   */

  FIXED_POINT_NORMALIZED_SIGNED {
    @Override
    public String descriptor()
    {
      return "FIXED_POINT_NORMALIZED_SIGNED";
    }
  },

  /**
   * The channel consists of unsigned scaled values; values are converted to
   * floating point values, so 0xff becomes 255.0.
   */

  SCALED_UNSIGNED {
    @Override
    public String descriptor()
    {
      return "SCALED_UNSIGNED";
    }
  },

  /**
   * The channel consists of signed scaled values; values are converted to
   * floating point values, so -32 becomes -32.0.
   */

  SCALED_SIGNED {
    @Override
    public String descriptor()
    {
      return "SCALED_SIGNED";
    }
  },

  /**
   * The channel consists of unsigned integer values.
   */

  INTEGER_UNSIGNED {
    @Override
    public String descriptor()
    {
      return "INTEGER_UNSIGNED";
    }
  },

  /**
   * The channel consists of signed integer values.
   */

  INTEGER_SIGNED {
    @Override
    public String descriptor()
    {
      return "INTEGER_SIGNED";
    }
  },

  /**
   * The channel consists of signed IEE754 floating point values.
   */

  FLOATING_POINT_IEEE754_SIGNED {
    @Override
    public String descriptor()
    {
      return "FLOATING_POINT_IEEE754_SIGNED";
    }
  },

  /**
   * The channel consists of unsigned IEE754 floating point values.
   */

  FLOATING_POINT_IEEE754_UNSIGNED {
    @Override
    public String descriptor()
    {
      return "FLOATING_POINT_IEEE754_UNSIGNED";
    }
  },
}
