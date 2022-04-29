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
import java.util.List;
import java.util.Optional;

import static com.io7m.calino.api.CLNIdentifiers.sectionEndIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImage2DIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageArrayIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageCubeIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageInfoIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionMetadataIdentifier;

/**
 * A readable file.
 */

public interface CLNFileReadableType extends Closeable
{
  /**
   * @return The list of sections in the file
   */

  List<CLNFileSectionDescription> sections();

  /**
   * @return The file version
   */

  CLNVersion version();

  /**
   * Open a section for reading.
   *
   * @param description The section description
   *
   * @return A readable section
   */

  CLNSectionReadableType openSection(
    CLNFileSectionDescription description);

  /**
   * @return The first available image info section, if one exists
   */

  default Optional<CLNSectionReadableImageInfoType> openImageInfo()
  {
    for (final var section : this.sections()) {
      final var description = section.description();
      if (description.identifier() == sectionImageInfoIdentifier()) {
        return Optional.of(
          (CLNSectionReadableImageInfoType) this.openSection(section)
        );
      }
    }
    return Optional.empty();
  }

  /**
   * @return The first available image 2D section, if one exists
   */

  default Optional<CLNSectionReadableImage2DType> openImage2D()
  {
    for (final var section : this.sections()) {
      final var description = section.description();
      if (description.identifier() == sectionImage2DIdentifier()) {
        return Optional.of(
          (CLNSectionReadableImage2DType) this.openSection(section)
        );
      }
    }
    return Optional.empty();
  }

  /**
   * @return The first available image cube section, if one exists
   */

  default Optional<CLNSectionReadableImageCubeType> openImageCube()
  {
    for (final var section : this.sections()) {
      final var description = section.description();
      if (description.identifier() == sectionImageCubeIdentifier()) {
        return Optional.of(
          (CLNSectionReadableImageCubeType) this.openSection(section)
        );
      }
    }
    return Optional.empty();
  }

  /**
   * @return The first available image array section, if one exists
   */

  default Optional<CLNSectionReadableImageArrayType> openImageArray()
  {
    for (final var section : this.sections()) {
      final var description = section.description();
      if (description.identifier() == sectionImageArrayIdentifier()) {
        return Optional.of(
          (CLNSectionReadableImageArrayType) this.openSection(section)
        );
      }
    }
    return Optional.empty();
  }

  /**
   * @return The first available metadata section, if one exists
   */

  default Optional<CLNSectionReadableMetadataType> openMetadata()
  {
    for (final var section : this.sections()) {
      final var description = section.description();
      if (description.identifier() == sectionMetadataIdentifier()) {
        return Optional.of(
          (CLNSectionReadableMetadataType) this.openSection(section)
        );
      }
    }
    return Optional.empty();
  }

  /**
   * @return The first available end section, if one exists
   */

  default Optional<CLNSectionReadableEndType> openEnd()
  {
    for (final var section : this.sections()) {
      final var description = section.description();
      if (description.identifier() == sectionEndIdentifier()) {
        return Optional.of(
          (CLNSectionReadableEndType) this.openSection(section)
        );
      }
    }
    return Optional.empty();
  }

  /**
   * Obtain the number of trailing octets in the file. This value should always
   * be zero for valid files.
   *
   * @return The number of trailing octets
   */

  long trailingOctets();
}
