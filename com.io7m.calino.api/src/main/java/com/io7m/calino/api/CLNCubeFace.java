/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

import java.util.List;

/**
 * The names of each of the faces of an axis-aligned cube.
 */

public enum CLNCubeFace
{
  /**
   * The face pointing towards positive infinity on the X axis.
   */

  X_POSITIVE,

  /**
   * The face pointing towards negative infinity on the X axis.
   */

  X_NEGATIVE,

  /**
   * The face pointing towards positive infinity on the Y axis.
   */

  Y_POSITIVE,

  /**
   * The face pointing towards negative infinity on the Y axis.
   */

  Y_NEGATIVE,

  /**
   * The face pointing towards positive infinity on the Z axis.
   */

  Z_POSITIVE,

  /**
   * The face pointing towards negative infinity on the Z axis.
   */

  Z_NEGATIVE;

  private static final List<CLNCubeFace> CUBE_FACES =
    List.of(
      X_POSITIVE,
      X_NEGATIVE,
      Y_POSITIVE,
      Y_NEGATIVE,
      Z_POSITIVE,
      Z_NEGATIVE
    );

  /**
   * @return The cube faces in specification order
   */

  public static List<CLNCubeFace> facesInOrder()
  {
    return CUBE_FACES;
  }

  /**
   * @return The short name of the cube face
   */

  public String shortName()
  {
    return switch (this) {
      case X_POSITIVE -> "xp";
      case X_NEGATIVE -> "xn";
      case Y_POSITIVE -> "yp";
      case Y_NEGATIVE -> "yn";
      case Z_POSITIVE -> "zp";
      case Z_NEGATIVE -> "zn";
    };
  }
}
