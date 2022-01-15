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
 * The texture coordinate S axis. This is typically considered to be analogous
 * the "width" or X axis.
 */

public enum CLNCoordinateAxisS implements CLNDescribableType
{
  /**
   * The S axis increases rightward.
   */

  AXIS_S_INCREASING_RIGHT {
    @Override
    public String descriptor()
    {
      return "SR";
    }
  },

  /**
   * The S axis increases leftward.
   */

  AXIS_S_INCREASING_LEFT {
    @Override
    public String descriptor()
    {
      return "SL";
    }
  };

  /**
   * Parse an S axis.
   *
   * @param segment The string
   *
   * @return A S axis
   */

  public static CLNCoordinateAxisS of(
    final String segment)
  {
    return switch (segment) {
      case "SR" -> AXIS_S_INCREASING_RIGHT;
      case "SL" -> AXIS_S_INCREASING_LEFT;
      default -> throw new IllegalArgumentException("Unparseable S axis");
    };
  }
}
