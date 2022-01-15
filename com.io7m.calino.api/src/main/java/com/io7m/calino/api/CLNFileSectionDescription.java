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
 * A description of a section within a file.
 *
 * @param fileOffset  The file offset
 * @param description The section description
 */

public record CLNFileSectionDescription(
  long fileOffset,
  CLNSectionDescription description)
{
  /**
   * A description of a section within a file.
   *
   * @param fileOffset  The file offset
   * @param description The section description
   */

  public CLNFileSectionDescription
  {
    Objects.requireNonNull(description, "description");
  }

  /**
   * Each section carries a fixed 16-byte header. The section data begins
   * directly after this header.
   *
   * @return The absolute file offset of the section's data
   */

  public long fileOffsetData()
  {
    return this.fileOffset + 16L;
  }

  /**
   * @return A description of the section as a human-readable string
   */

  public String show()
  {
    final var nameOpt =
      CLNIdentifiers.nameOf(this.description.identifier());

    if (nameOpt.isPresent()) {
      return String.format(
        "%s (%s) @%s size %s",
        nameOpt.get(),
        Long.toUnsignedString(this.description.identifier(), 16),
        Long.toUnsignedString(this.fileOffset, 16),
        Long.toUnsignedString(this.description.size(), 16)
      );
    }

    return String.format(
      "%s @%s size %s",
      Long.toUnsignedString(this.description.identifier(), 16),
      Long.toUnsignedString(this.fileOffset, 16),
      Long.toUnsignedString(this.description.size(), 16)
    );
  }
}
