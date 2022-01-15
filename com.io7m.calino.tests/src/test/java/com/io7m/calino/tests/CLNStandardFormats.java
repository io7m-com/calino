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

package com.io7m.calino.tests;

import com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard;
import com.io7m.calino.api.CLNChannelsTypeDescriptionStandard;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class CLNStandardFormats
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNStandardFormats.class);

  @Test
  public void testLayoutAlignments()
  {
    final var descriptions =
      CLNChannelsLayoutDescriptionStandard.values();

    for (final var description : descriptions) {
      final var alignment = description.texelBlockAlignment();
      LOG.debug(
        "{}: align {}",
        description,
        Integer.valueOf(alignment)
      );

      assertTrue(alignment >= 1);
      assertTrue(alignment <= 32);
    }
  }

  @Test
  public void testLayoutUniqueDescriptors()
  {
    final var descriptions =
      CLNChannelsLayoutDescriptionStandard.values();

    final var descriptors =
      new HashSet<String>();

    for (final var description : descriptions) {
      descriptors.add(description.descriptor());
    }

    assertEquals(descriptors.size(), descriptions.length);
  }

  @Test
  public void testTypeUniqueDescriptors()
  {
    final var descriptions =
      CLNChannelsTypeDescriptionStandard.values();

    final var descriptors =
      new HashSet<String>();

    for (final var description : descriptions) {
      descriptors.add(description.descriptor());
    }

    assertEquals(descriptors.size(), descriptions.length);
  }
}
