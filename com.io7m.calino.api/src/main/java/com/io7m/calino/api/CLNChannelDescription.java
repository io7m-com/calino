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
import java.util.regex.Pattern;

/**
 * A description of a single image channel.
 *
 * @param semantic The channel semantic
 * @param bits     The size of the channel in bits
 */

public record CLNChannelDescription(
  CLNChannelSemantic semantic,
  int bits)
  implements CLNDescribableType
{
  private static final Pattern VALID_CHANNEL_DESCRIPTION =
    Pattern.compile("([A-Z]+)([0-9]+)");

  /**
   * A description of a single image channel.
   *
   * @param semantic The channel semantic
   * @param bits     The size of the channel in bits
   */

  public CLNChannelDescription
  {
    Objects.requireNonNull(semantic, "semantic");

    if (bits == 0) {
      throw new IllegalArgumentException(
        "Channel must have a non-zero bit count");
    }
  }

  /**
   * Parse a channel descriptor.
   *
   * @param text The descriptor
   *
   * @return A parsed description
   *
   * @throws ParseException On parse errors
   */

  public static CLNChannelDescription parse(
    final String text)
    throws ParseException
  {
    final var matcher = VALID_CHANNEL_DESCRIPTION.matcher(text);
    if (matcher.matches()) {
      final var semT = matcher.group(1);
      final var numT = matcher.group(2);
      return new CLNChannelDescription(
        CLNChannelSemantic.of(semT),
        Integer.parseUnsignedInt(numT)
      );
    }

    throw parseError(text, 0);
  }

  private static ParseException parseError(
    final String text,
    final int index)
  {
    final var error = new StringBuilder(128);
    final var lineSeparator = System.lineSeparator();
    error.append("Unparsable channel description.");
    error.append(lineSeparator);
    error.append("  At: Index ");
    error.append(index);
    error.append(lineSeparator);
    error.append("  Expected: ");
    error.append(VALID_CHANNEL_DESCRIPTION.toString());
    error.append(lineSeparator);
    error.append("  Examples: R32, G8, etc");
    error.append(lineSeparator);
    error.append("  Received: ");
    error.append(text);
    error.append(lineSeparator);
    return new ParseException(error.toString(), index);
  }

  @Override
  public String descriptor()
  {
    return this.semantic.descriptor() + Integer.toUnsignedString(this.bits);
  }
}
