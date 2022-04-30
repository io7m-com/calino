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
import java.util.Objects;
import java.util.Optional;

/**
 * A custom channel layout description.
 *
 * @param channels The channels
 * @param packing  The packing specification
 */

public record CLNChannelsLayoutDescriptionCustom(
  List<CLNChannelDescription> channels,
  Optional<CLNChannelLayoutPacking> packing
) implements CLNChannelsLayoutDescriptionType
{
  /**
   * A custom channel layout description.
   *
   * @param channels The channels
   * @param packing  The packing specification
   */

  public CLNChannelsLayoutDescriptionCustom
  {
    Objects.requireNonNull(channels, "channels");

    final var bitsChan =
      CLNChannelsLayoutDescriptions.totalBits(channels);

    if (packing.isPresent()) {
      final var p = packing.get();
      final var bitsPack = p.bitCount();
      if (bitsChan != bitsPack) {
        throw new IllegalArgumentException(
          "Total channel bits must equal packed value " + bitsPack);
      }
    } else {
      for (final var channel : channels) {
        if (channel.bits() % 8 != 0) {
          throw new IllegalArgumentException(
            "For non-packed layouts, channel sizes must be evenly divisible by 8"
          );
        }
      }
    }
  }
}
