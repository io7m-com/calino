/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.calino.vanilla.internal;

import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.api.CLNSectionReadableImageArrayType;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableType;
import com.io7m.calino.validation.api.CLNValidationError;

import java.net.URI;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.calino.validation.api.CLNValidationStatus.STATUS_ERROR;

/**
 * A factory of errors.
 */

public final class CLN1ValidationErrors
{
  private final CLN1ValidationStrings strings;
  private final URI source;

  /**
   * A factory of errors.
   *
   * @param inSource  The source file
   * @param inStrings The error strings
   */

  public CLN1ValidationErrors(
    final URI inSource,
    final CLN1ValidationStrings inStrings)
  {
    this.source =
      Objects.requireNonNull(inSource, "source");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
  }

  /**
   * Construct an error.
   *
   * @param section The section
   * @param e       The exception
   *
   * @return An error
   */

  public CLNValidationError errorOfException(
    final CLNSectionReadableType section,
    final Exception e)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.empty(),
      e.getMessage(),
      Optional.of(e)
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   * @param e       The exception
   * @param message The message
   *
   * @return An error
   */

  public CLNValidationError errorOfException(
    final CLNSectionReadableType section,
    final Exception e,
    final String message)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.empty(),
      "%s: %s".formatted(message, e.getMessage()),
      Optional.of(e)
    );
  }

  /**
   * Construct an error.
   *
   * @param section      The section
   * @param mipMap       The mipMap
   * @param sizeReceived The received size
   *
   * @return An error
   */

  public CLNValidationError error2DCompressedDataSizeMismatch(
    final CLNSectionReadableType section,
    final CLNImage2DDescription mipMap,
    final long sizeReceived)
  {
    final var baseOffset =
      section.fileSectionDescription().fileOffsetData();
    final var offset =
      baseOffset + mipMap.dataOffsetWithinSection();

    return new CLNValidationError(
      this.source,
      offset,
      STATUS_ERROR,
      Optional.of(UUID.fromString("e676eaef-f25a-44e8-9360-bcfaf35ce1e6")),
      this.strings.format(
        "error2DCompressedSizeMismatch",
        Integer.toUnsignedString(mipMap.mipMapLevel()),
        Long.toUnsignedString(mipMap.dataSizeUncompressed()),
        Long.toUnsignedString(sizeReceived)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section       The section
   * @param mipMap        The mipMap
   * @param crc32Received The CRC32
   *
   * @return An error
   */

  public CLNValidationError error2DUncompressedDataCRC32Mismatch(
    final CLNSectionReadableImage2DType section,
    final CLNImage2DDescription mipMap,
    final long crc32Received)
  {
    final var baseOffset =
      section.fileSectionDescription().fileOffsetData();
    final var offset =
      baseOffset + mipMap.dataOffsetWithinSection();

    return new CLNValidationError(
      this.source,
      offset,
      STATUS_ERROR,
      Optional.of(UUID.fromString("e676eaef-f25a-44e8-9360-bcfaf35ce1e6")),
      this.strings.format(
        "error2DUncompressedCRC32Mismatch",
        Integer.toUnsignedString(mipMap.mipMapLevel()),
        Integer.toUnsignedString(mipMap.crc32Uncompressed(), 16),
        Long.toUnsignedString(crc32Received, 16)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   * @param sizeZ   The Z size
   *
   * @return An error
   */

  public CLNValidationError error2DExpectedSizeZ1(
    final CLNSectionReadableImageInfoType section,
    final int sizeZ)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("909468f0-a253-4e8f-82ff-6a6909bf1220")),
      this.strings.format(
        "error2DExpectedSizeZ1",
        Integer.toUnsignedString(sizeZ)),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   * @param level   The level
   *
   * @return An error
   */

  public CLNValidationError error2DMipLevelDuplicate(
    final CLNSectionReadableImage2DType section,
    final int level)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("f868cdeb-21ce-4b89-9c2d-b1383b07cbd7")),
      this.strings.format(
        "error2DMipLevelDuplicate",
        Integer.toUnsignedString(level)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section    The section
   * @param mipHighest The highest mip level
   *
   * @return An error
   */

  public CLNValidationError error2DMipLevelGaps(
    final CLNSectionReadableImage2DType section,
    final int mipHighest)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("f868cdeb-21ce-4b89-9c2d-b1383b07cbd7")),
      this.strings.format(
        "error2DMipLevelGaps",
        Integer.toUnsignedString(mipHighest)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @return An error
   */

  public CLNValidationError errorImageDataNotPresent()
  {
    return new CLNValidationError(
      this.source,
      0L,
      STATUS_ERROR,
      Optional.of(UUID.fromString("2803ef9e-a1de-4d28-a0ab-a03eec53582e")),
      this.strings.format("errorImageDataPresent"),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section      The section
   * @param mipMap       The mipMap
   * @param sizeReceived The received size
   *
   * @return An error
   */

  public CLNValidationError errorArrayCompressedDataSizeMismatch(
    final CLNSectionReadableType section,
    final CLNImageArrayDescription mipMap,
    final long sizeReceived)
  {
    final var baseOffset =
      section.fileSectionDescription().fileOffsetData();
    final var offset =
      baseOffset + mipMap.dataOffsetWithinSection();

    return new CLNValidationError(
      this.source,
      offset,
      STATUS_ERROR,
      Optional.of(UUID.fromString("4d7423ef-2f74-4612-9685-1615ea0c5c7e")),
      this.strings.format(
        "errorArrayCompressedSizeMismatch",
        Integer.toUnsignedString(mipMap.layer()),
        Integer.toUnsignedString(mipMap.mipMapLevel()),
        Long.toUnsignedString(mipMap.dataSizeUncompressed()),
        Long.toUnsignedString(sizeReceived)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section       The section
   * @param mipMap        The mipMap
   * @param crc32Received The CRC32
   *
   * @return An error
   */

  public CLNValidationError errorArrayUncompressedDataCRC32Mismatch(
    final CLNSectionReadableType section,
    final CLNImageArrayDescription mipMap,
    final long crc32Received)
  {
    final var baseOffset =
      section.fileSectionDescription().fileOffsetData();
    final var offset =
      baseOffset + mipMap.dataOffsetWithinSection();

    return new CLNValidationError(
      this.source,
      offset,
      STATUS_ERROR,
      Optional.of(UUID.fromString("4d7423ef-2f74-4612-9685-1615ea0c5c7e")),
      this.strings.format(
        "errorArrayUncompressedCRC32Mismatch",
        Integer.toUnsignedString(mipMap.layer()),
        Integer.toUnsignedString(mipMap.mipMapLevel()),
        Integer.toUnsignedString(mipMap.crc32Uncompressed(), 16),
        Long.toUnsignedString(crc32Received, 16)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @return An error
   */

  public CLNValidationError errorImageInfoNotPresent()
  {
    return new CLNValidationError(
      this.source,
      0L,
      STATUS_ERROR,
      Optional.of(UUID.fromString("2d4988b3-86e5-4bbe-8fbe-526b5b2b16d5")),
      this.strings.format("errorImageInfoNotPresent"),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   * @param layer   The layer
   * @param level   The mip level
   *
   * @return An error
   */

  public CLNValidationError errorArrayMipNotUnique(
    final CLNSectionReadableImageArrayType section,
    final int level,
    final int layer)
  {
    final var baseOffset =
      section.fileSectionDescription().fileOffsetData();

    return new CLNValidationError(
      this.source,
      baseOffset,
      STATUS_ERROR,
      Optional.of(UUID.fromString("8729926f-ca1d-4b06-a7bb-295ecd38d12a")),
      this.strings.format(
        "errorArrayMipNotUnique",
        Integer.toUnsignedString(layer),
        Integer.toUnsignedString(level)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section    The section
   * @param mipHighest The highest mip level
   *
   * @return An error
   */

  public CLNValidationError errorArrayMipLevelGaps(
    final CLNSectionReadableImageArrayType section,
    final int mipHighest)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("8729926f-ca1d-4b06-a7bb-295ecd38d12a")),
      this.strings.format(
        "errorArrayMipLevelGaps",
        Integer.toUnsignedString(mipHighest)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section      The section
   * @param level        The mip level
   * @param layerHighest The highest layer
   * @param receivedLayers The received layers
   * @return An error
   */

  public CLNValidationError errorArrayMipLayerGaps(
    final CLNSectionReadableImageArrayType section,
    final int level,
    final int layerHighest,
    final Set<Integer> receivedLayers)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("8729926f-ca1d-4b06-a7bb-295ecd38d12a")),
      this.strings.format(
        "errorArrayMipLayerGaps",
        Integer.toUnsignedString(level),
        Integer.toUnsignedString(layerHighest),
        formatSet(receivedLayers)
      ),
      Optional.empty()
    );
  }

  private static String formatSet(
    final Set<Integer> set)
  {
    return set.toString()
      .replace('[', '{')
      .replace(']', '}');
  }

  /**
   * Construct an error.
   *
   * @param section      The section
   * @param layerHighest The mip level
   * @param sizeZ        The declared Z size
   *
   * @return An error
   */

  public CLNValidationError errorArrayLayerCount(
    final CLNSectionReadableImageArrayType section,
    final int sizeZ,
    final int layerHighest)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("cb73941f-ab0c-46cd-a8a2-94ca912eda3a")),
      this.strings.format(
        "errorArrayLayerCount",
        Integer.toUnsignedString(sizeZ),
        Integer.toUnsignedString(layerHighest)
      ),
      Optional.empty()
    );
  }
}
