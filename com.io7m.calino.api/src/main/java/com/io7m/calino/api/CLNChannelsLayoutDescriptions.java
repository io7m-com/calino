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
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * Functions over layout descriptions.
 */

public final class CLNChannelsLayoutDescriptions
{
  private CLNChannelsLayoutDescriptions()
  {

  }

  /**
   * Determine the total required bits of the list of channels.
   *
   * @param channels The channels
   *
   * @return The total bits
   */

  public static int totalBits(
    final List<CLNChannelDescription> channels)
  {
    var total = 0;
    for (final var channel : channels) {
      total += channel.bits();
    }
    return total;
  }

  /**
   * Parse a layout descriptor.
   *
   * @param text The descriptor
   *
   * @return A parsed layout
   *
   * @throws ParseException On errors
   */

  public static CLNChannelsLayoutDescriptionType parseLayoutDescriptor(
    final String text)
    throws ParseException
  {
    final var knownFormats =
      CLNChannelsLayoutDescriptionStandard.values();

    for (final var known : knownFormats) {
      if (Objects.equals(known.descriptor(), text)) {
        return known;
      }
    }

    final var baseSegments = text.split("\\|");
    return switch (baseSegments.length) {
      case 1 -> {
        yield new CLNChannelsLayoutDescriptionCustom(
          parseDescriptions(baseSegments[0]),
          Optional.empty()
        );
      }
      case 2 -> {
        yield new CLNChannelsLayoutDescriptionCustom(
          parseDescriptions(baseSegments[1]),
          Optional.of(CLNChannelLayoutPacking.parse(baseSegments[0]))
        );
      }
      default -> {
        final var lineSeparator = System.lineSeparator();
        throw new ParseException(
          new StringBuilder(64)
            .append("Unparseable descriptor.")
            .append(lineSeparator)
            .append("  Expected: (<packing> '|')? <layout>+")
            .append(lineSeparator)
            .append("  Received: ")
            .append(text)
            .append(lineSeparator)
            .toString(),
          0
        );
      }
    };
  }

  private static List<CLNChannelDescription> parseDescriptions(
    final String text)
    throws ParseException
  {
    final var descriptions = new ArrayList<CLNChannelDescription>();
    final var channelSegments = text.split(":");
    for (final var channelSegment : channelSegments) {
      descriptions.add(CLNChannelDescription.parse(channelSegment));
    }
    return List.copyOf(descriptions);
  }
}
