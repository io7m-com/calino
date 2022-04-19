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

import java.io.Closeable;
import java.io.IOException;
import java.util.List;

import static com.io7m.calino.api.CLNIdentifiers.sectionEndIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImage2DIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageArrayIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageInfoIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionMetadataIdentifier;

/**
 * A writable file.
 */

public interface CLNFileWritableType extends Closeable
{
  /**
   * @return The sections currently declared within the file
   *
   * @throws IOException On errors
   */

  List<CLNFileSectionDescription> sections()
    throws IOException;

  /**
   * @return The file version
   */

  CLNVersion version();

  /**
   * Create a new section with the given identifier.
   *
   * @param identifier The identifier
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  CLNSectionWritableType createSection(long identifier)
    throws IOException;

  /**
   * Create a new image info section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default CLNSectionWritableImageInfoType createSectionImageInfo()
    throws IOException
  {
    return (CLNSectionWritableImageInfoType)
      this.createSection(sectionImageInfoIdentifier());
  }

  /**
   * Create a new metadata section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default CLNSectionWritableMetadataType createSectionMetadata()
    throws IOException
  {
    return (CLNSectionWritableMetadataType)
      this.createSection(sectionMetadataIdentifier());
  }

  /**
   * Create a new end section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default CLNSectionWritableEndType createSectionEnd()
    throws IOException
  {
    return (CLNSectionWritableEndType)
      this.createSection(sectionEndIdentifier());
  }

  /**
   * Create a new image 2D section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default CLNSectionWritableImage2DType createSectionImage2D()
    throws IOException
  {
    return (CLNSectionWritableImage2DType)
      this.createSection(sectionImage2DIdentifier());
  }

  /**
   * Create a new image array section.
   *
   * @return A new section
   *
   * @throws IOException On errors
   */

  default CLNSectionWritableImageArrayType createSectionImageArray()
    throws IOException
  {
    return (CLNSectionWritableImageArrayType)
      this.createSection(sectionImageArrayIdentifier());
  }
}
