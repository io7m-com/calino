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
 * The texture coordinate R axis. This is typically considered to be the "depth"
 * or Z axis.
 */

public enum CLNCoordinateAxisR implements CLNDescribableType
{
  /**
   * The R axis increases towards the viewer.
   */

  AXIS_R_INCREASING_TOWARD {
    @Override
    public String descriptor()
    {
      return "RT";
    }
  },

  /**
   * The R axis increases away from the viewer.
   */

  AXIS_R_INCREASING_AWAY {
    @Override
    public String descriptor()
    {
      return "RA";
    }
  };

  /**
   * Parse an R axis.
   *
   * @param segment The string
   *
   * @return An R axis
   */

  public static CLNCoordinateAxisR of(
    final String segment)
  {
    return switch (segment) {
      case "RT" -> AXIS_R_INCREASING_TOWARD;
      case "RA" -> AXIS_R_INCREASING_AWAY;
      default -> throw new IllegalArgumentException("Unparseable R axis");
    };
  }
}
