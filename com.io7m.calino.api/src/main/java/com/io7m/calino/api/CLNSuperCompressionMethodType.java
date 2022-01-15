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

import java.util.Objects;

/**
 * A supercompression method. This refers to compression that is used on data
 * that must be decompressed on the CPU before it can be uploaded to a GPU for
 * use. This is in contrast to <i>compression</i> which is used to compress data
 * in a manner that can be decompressed by a GPU in realtime.
 *
 * @see CLNCompressionMethodType
 */

public sealed interface CLNSuperCompressionMethodType
  extends CLNDescribableType
  permits CLNSuperCompressionMethodCustom,
  CLNSuperCompressionMethodStandard
{
  /**
   * Parse a descriptor as a super compression method.
   *
   * @param text              The descriptor
   * @param sectionIdentifier The required section identifier
   *
   * @return A super compression method
   */

  static CLNSuperCompressionMethodType parse(
    final String text,
    final long sectionIdentifier)
  {
    Objects.requireNonNull(text, "text");

    final var knownMethods =
      CLNSuperCompressionMethodStandard.values();
    for (final var known : knownMethods) {
      if (Objects.equals(text, known.descriptor())) {
        return known;
      }
    }
    return new CLNSuperCompressionMethodCustom(text, sectionIdentifier);
  }

  /**
   * @return The identifier of the section containing data required to
   * decompress data
   */

  long compressionSectionIdentifier();
}
