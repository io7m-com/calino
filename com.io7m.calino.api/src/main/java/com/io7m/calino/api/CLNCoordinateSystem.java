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
 * The coordinate system axis orientations.
 *
 * @param axisR The R axis orientation
 * @param axisS The S axis orientation
 * @param axisT The T axis orientation
 */

public record CLNCoordinateSystem(
  CLNCoordinateAxisR axisR,
  CLNCoordinateAxisS axisS,
  CLNCoordinateAxisT axisT)
  implements CLNDescribableType
{
  /**
   * The coordinate system axis orientations.
   *
   * @param axisR The R axis orientation
   * @param axisS The S axis orientation
   * @param axisT The T axis orientation
   */

  public CLNCoordinateSystem
  {
    Objects.requireNonNull(axisR, "axisR");
    Objects.requireNonNull(axisS, "axisS");
    Objects.requireNonNull(axisT, "axisT");
  }

  /**
   * Parse a coordinate system descriptor.
   *
   * @param text The descriptor text
   *
   * @return A coordinate system
   *
   * @throws ParseException On errors
   */

  public static CLNCoordinateSystem parseDescriptor(
    final String text)
    throws ParseException
  {
    final var segments = text.split(":");
    if (segments.length != 3) {
      throw new ParseException(
        "Coordinate system descriptors must be three-part strings", 0);
    }

    try {
      return new CLNCoordinateSystem(
        CLNCoordinateAxisR.of(segments[0]),
        CLNCoordinateAxisS.of(segments[1]),
        CLNCoordinateAxisT.of(segments[2])
      );
    } catch (final IllegalArgumentException e) {
      throw new ParseException(e.getMessage(), 0);
    }
  }

  @Override
  public String descriptor()
  {
    return new StringBuilder(8)
      .append(this.axisR.descriptor())
      .append(':')
      .append(this.axisS.descriptor())
      .append(':')
      .append(this.axisT.descriptor())
      .toString();
  }
}
