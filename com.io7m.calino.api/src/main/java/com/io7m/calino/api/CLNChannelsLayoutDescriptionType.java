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

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * The type of channel layout descriptions.
 */

public sealed interface CLNChannelsLayoutDescriptionType
  extends CLNDescribableType
  permits CLNChannelsLayoutDescriptionCustom,
  CLNChannelsLayoutDescriptionStandard
{
  @Override
  default String descriptor()
  {
    final var packText =
      this.packing()
        .map(p -> p.descriptor() + "|")
        .orElse("");

    final var channelsText =
      this.channels()
        .stream()
        .map(CLNChannelDescription::descriptor)
        .collect(Collectors.joining(":"));

    return packText + channelsText;
  }

  /**
   * @return The channel descriptions
   */

  List<CLNChannelDescription> channels();

  /**
   * @return The packing value, if any
   */

  Optional<CLNChannelLayoutPacking> packing();

  /**
   * @return The total number of bits in a single sample
   */

  default int bitsTotal()
  {
    return CLNChannelsLayoutDescriptions.totalBits(this.channels());
  }

  /**
   * @return The required alignment, in octets, of image data of this type
   */

  default int texelBlockAlignment()
  {
    final var b = this.bitsTotal();
    final int q = b / 8;
    final int r = b % 8;
    return (q * 8) + (r > 0 ? 1 : 0);
  }
}
