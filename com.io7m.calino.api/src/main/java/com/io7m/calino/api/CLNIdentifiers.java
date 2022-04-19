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

import java.util.Optional;

/**
 * The identifiers for standard sections.
 */

public final class CLNIdentifiers
{
  private static final long FILE_IDENTIFIER =
    0x8943_4C4E_0D0A_1A0AL;
  private static final long SECTION_END_IDENTIFIER =
    0x434C_4E5F_454E_4421L;
  private static final long SECTION_IMAGE_INFO_IDENTIFIER =
    0x434C_4E49_494E_464FL;
  private static final long SECTION_METADATA_IDENTIFIER =
    0x434C_4E5F_4D45_5441L;
  private static final long SECTION_IMAGE_2D_IDENTIFIER =
    0x434C_4E5F_4932_4421L;
  private static final long SECTION_IMAGE_ARRAY_IDENTIFIER =
    0x434C_4E5F_4152_5221L;

  private CLNIdentifiers()
  {

  }

  /**
   * @return The identifier used to identify <tt>calino</tt> files
   */

  public static long fileIdentifier()
  {
    return FILE_IDENTIFIER;
  }

  /**
   * @return The identifier used to identify <tt>end</tt> sections
   */

  public static long sectionEndIdentifier()
  {
    return SECTION_END_IDENTIFIER;
  }

  /**
   * @return The identifier used to identify <tt>image info</tt> sections
   */

  public static long sectionImageInfoIdentifier()
  {
    return SECTION_IMAGE_INFO_IDENTIFIER;
  }

  /**
   * @return The identifier used to identify <tt>image 2D</tt> sections
   */

  public static long sectionImage2DIdentifier()
  {
    return SECTION_IMAGE_2D_IDENTIFIER;
  }

  /**
   * @return The identifier used to identify <tt>metadata</tt> sections
   */

  public static long sectionMetadataIdentifier()
  {
    return SECTION_METADATA_IDENTIFIER;
  }

  /**
   * @return The identifier used to identify <tt>image array</tt> sections
   */

  public static long sectionImageArrayIdentifier()
  {
    return SECTION_IMAGE_ARRAY_IDENTIFIER;
  }

  /**
   * Determine a humanly-readable name of an identifier.
   *
   * @param identifier The identifier
   *
   * @return A humanly-readable name, if one is known
   */

  public static Optional<String> nameOf(
    final long identifier)
  {
    if (identifier == SECTION_IMAGE_INFO_IDENTIFIER) {
      return Optional.of("IMAGE_INFO");
    }
    if (identifier == SECTION_IMAGE_2D_IDENTIFIER) {
      return Optional.of("IMAGE_2D");
    }
    if (identifier == SECTION_METADATA_IDENTIFIER) {
      return Optional.of("METADATA");
    }
    if (identifier == SECTION_END_IDENTIFIER) {
      return Optional.of("END");
    }
    if (identifier == SECTION_IMAGE_ARRAY_IDENTIFIER) {
      return Optional.of("IMAGE_ARRAY");
    }
    return Optional.empty();
  }
}
