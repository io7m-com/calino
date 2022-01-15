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
import java.util.Comparator;
import java.util.Objects;
import java.util.regex.Pattern;

import static java.lang.Integer.toUnsignedString;

/**
 * A version number.
 *
 * @param major The major version
 * @param minor The minor version
 */

public record CLNVersion(
  int major,
  int minor)
  implements Comparable<CLNVersion>
{
  private static final Pattern VALID_VERSION =
    Pattern.compile("([0-9]+)\\.([0-9]+)");

  /**
   * Parse a version string.
   *
   * @param text The text
   *
   * @return A version string
   *
   * @throws ParseException On parse errors
   */

  public static CLNVersion parse(
    final String text)
    throws ParseException
  {
    Objects.requireNonNull(text, "text");

    final var matcher = VALID_VERSION.matcher(text);
    if (matcher.matches()) {
      return new CLNVersion(
        Integer.parseUnsignedInt(matcher.group(1)),
        Integer.parseUnsignedInt(matcher.group(2))
      );
    }

    final var lineSeparator = System.lineSeparator();
    throw new ParseException(
      new StringBuilder(64)
        .append("Invalid version string.")
        .append(lineSeparator)
        .append("  Expected: ")
        .append(VALID_VERSION.pattern())
        .append(lineSeparator)
        .append("  Received: ")
        .append(text)
        .append(lineSeparator)
        .toString(),
      0
    );
  }

  @Override
  public String toString()
  {
    return String.format(
      "%s.%s",
      toUnsignedString(this.major),
      toUnsignedString(this.minor)
    );
  }

  @Override
  public int compareTo(final CLNVersion other)
  {
    return ((Comparator<CLNVersion>) (ox, oy) -> {
      return Integer.compareUnsigned(ox.major, oy.major);
    }).thenComparing((ox, oy) -> {
      return Integer.compareUnsigned(ox.minor, oy.minor);
    }).compare(this, other);
  }
}
