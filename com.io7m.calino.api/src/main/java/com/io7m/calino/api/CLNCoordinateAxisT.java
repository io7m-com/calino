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
 * The texture coordinate T axis. This is typically considered to be analogous
 * to the "height" or Y axis.
 */

public enum CLNCoordinateAxisT implements CLNDescribableType
{
  /**
   * The T axis increases downward.
   */

  AXIS_T_INCREASING_DOWN {
    @Override
    public String descriptor()
    {
      return "TD";
    }
  },

  /**
   * The T axis increases upward.
   */

  AXIS_T_INCREASING_UP {
    @Override
    public String descriptor()
    {
      return "TU";
    }
  };

  /**
   * Parse an T axis.
   *
   * @param segment The string
   *
   * @return A T axis
   */

  public static CLNCoordinateAxisT of(
    final String segment)
  {
    return switch (segment) {
      case "TD" -> AXIS_T_INCREASING_DOWN;
      case "TU" -> AXIS_T_INCREASING_UP;
      default -> throw new IllegalArgumentException("Unparseable T axis");
    };
  }
}
