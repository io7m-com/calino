/*
 * Copyright © 2026 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

package com.io7m.calino.vanilla;

import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.entomos.core.EoFileDescription;
import com.io7m.entomos.core.EoFileSectionDescription;
import com.io7m.entomos.core.EoFileVersionsDescription;
import com.io7m.entomos.core.EoSectionCardinality;
import com.io7m.entomos.core.EoSectionOrdering;

/**
 * The file format definitions.
 */

public final class CLNFileFormats
{
  private static final EoFileDescription FILE_FORMAT_2 =
    createFileFormat1();
  private static final EoFileVersionsDescription FILE_FORMATS =
    createFileFormats();

  private CLNFileFormats()
  {

  }

  /**
   * @return The file format versions
   */

  public static EoFileVersionsDescription fileFormats()
  {
    return FILE_FORMATS;
  }

  private static EoFileVersionsDescription createFileFormats()
  {
    return EoFileVersionsDescription.builder()
      .addDescriptions(fileFormat2())
      .build();
  }

  /**
   * @return The version 2 file format.
   */

  public static EoFileDescription fileFormat2()
  {
    return FILE_FORMAT_2;
  }

  private static EoFileDescription createFileFormat1()
  {
    final var imageInfo =
      EoFileSectionDescription.builder()
        .setTag(CLNIdentifiers.sectionImageInfoIdentifier())
        .setCardinality(EoSectionCardinality.ONE)
        .setOrdering(EoSectionOrdering.MUST_BE_FIRST)
        .build();

    final var image2d =
      EoFileSectionDescription.builder()
        .setTag(CLNIdentifiers.sectionImage2DIdentifier())
        .setOrdering(EoSectionOrdering.ANY_ORDER)
        .setCardinality(EoSectionCardinality.ZERO_TO_ONE)
        .build();

    final var imageCube =
      EoFileSectionDescription.builder()
        .setTag(CLNIdentifiers.sectionImageCubeIdentifier())
        .setOrdering(EoSectionOrdering.ANY_ORDER)
        .setCardinality(EoSectionCardinality.ZERO_TO_ONE)
        .build();

    final var imageArray =
      EoFileSectionDescription.builder()
        .setTag(CLNIdentifiers.sectionImageArrayIdentifier())
        .setOrdering(EoSectionOrdering.ANY_ORDER)
        .setCardinality(EoSectionCardinality.ZERO_TO_ONE)
        .build();

    final var meta =
      EoFileSectionDescription.builder()
        .setTag(CLNIdentifiers.sectionMetadataIdentifier())
        .setOrdering(EoSectionOrdering.ANY_ORDER)
        .setCardinality(EoSectionCardinality.ZERO_TO_ONE)
        .build();

    return EoFileDescription.builder()
      .setFileTag(CLNIdentifiers.fileIdentifier())
      .setEndTag(CLNIdentifiers.sectionEndIdentifier())
      .addSections(imageInfo)
      .addSections(image2d)
      .addSections(imageCube)
      .addSections(imageArray)
      .addSections(meta)
      .setVersionMajor(2)
      .setVersionMinor(0)
      .build();
  }
}
