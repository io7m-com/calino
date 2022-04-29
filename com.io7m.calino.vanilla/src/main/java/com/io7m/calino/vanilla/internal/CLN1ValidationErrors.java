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

import com.io7m.calino.api.CLNCubeFace;
import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNImageCubeDescription;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.api.CLNSectionReadableImageArrayType;
import com.io7m.calino.api.CLNSectionReadableImageCubeType;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableType;
import com.io7m.calino.validation.api.CLNValidationError;

import java.net.URI;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.calino.validation.api.CLNValidationStatus.STATUS_ERROR;
import static com.io7m.calino.validation.api.CLNValidationStatus.STATUS_WARNING;

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
   * @param section        The section
   * @param level          The mip level
   * @param layerHighest   The highest layer
   * @param receivedLayers The received layers
   *
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

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param description The description
   *
   * @return An error
   */

  public CLNValidationError warnArrayUncompressedDataSizeMismatch(
    final CLNSectionReadableImageArrayType section,
    final CLNImageArrayDescription description)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("4d7423ef-2f74-4612-9685-1615ea0c5c7e")),
      this.strings.format(
        "warnArrayUncompressedDataSizeMismatch",
        Long.toUnsignedString(description.dataSizeCompressed()),
        Long.toUnsignedString(description.dataSizeUncompressed()),
        Integer.toUnsignedString(description.layer()),
        Integer.toUnsignedString(description.mipMapLevel())
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param description The description
   *
   * @return An error
   */

  public CLNValidationError warn2DUncompressedDataSizeMismatch(
    final CLNSectionReadableImage2DType section,
    final CLNImage2DDescription description)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("4d7423ef-2f74-4612-9685-1615ea0c5c7e")),
      this.strings.format(
        "warn2DUncompressedDataSizeMismatch",
        Long.toUnsignedString(description.dataSizeCompressed()),
        Long.toUnsignedString(description.dataSizeUncompressed()),
        Integer.toUnsignedString(description.mipMapLevel())
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param description The description
   *
   * @return An error
   */

  public CLNValidationError warnArrayCompressedSizeZero(
    final CLNSectionReadableImageArrayType section,
    final CLNImageArrayDescription description)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("0afd8e85-daa5-459a-af8e-6657716959b0")),
      this.strings.format(
        "warnArrayCompressedSizeZero",
        Integer.toUnsignedString(description.layer()),
        Integer.toUnsignedString(description.mipMapLevel())
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param description The description
   *
   * @return An error
   */

  public CLNValidationError warn2DCompressedSizeZero(
    final CLNSectionReadableImage2DType section,
    final CLNImage2DDescription description)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("2c3420bb-1273-4f1e-9212-9f259d60d6f1")),
      this.strings.format(
        "warn2DCompressedSizeZero",
        Integer.toUnsignedString(description.mipMapLevel())
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param description The description
   *
   * @return An error
   */

  public CLNValidationError warnArrayUncompressedSizeZero(
    final CLNSectionReadableImageArrayType section,
    final CLNImageArrayDescription description)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("5a5a6f15-82f6-4188-8417-e1e0a0e37fc1")),
      this.strings.format(
        "warnArrayUncompressedSizeZero",
        Integer.toUnsignedString(description.layer()),
        Integer.toUnsignedString(description.mipMapLevel())
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param description The description
   *
   * @return An error
   */

  public CLNValidationError warn2DUncompressedSizeZero(
    final CLNSectionReadableImage2DType section,
    final CLNImage2DDescription description)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("41c816ac-d7ee-4041-a764-9a36a983080c")),
      this.strings.format(
        "warn2DUncompressedSizeZero",
        Integer.toUnsignedString(description.mipMapLevel())
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   *
   * @return An error
   */

  public CLNValidationError error2DNoMipmaps(
    final CLNSectionReadableImage2DType section)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("f868cdeb-21ce-4b89-9c2d-b1383b07cbd7")),
      this.strings.format("error2DNoMipmaps"),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   *
   * @return An error
   */

  public CLNValidationError errorArrayNoMipmaps(
    final CLNSectionReadableImageArrayType section)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("cf42f33c-e410-42b9-8cb8-ef1d5a7d044f")),
      this.strings.format("errorArrayNoMipmaps"),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   *
   * @return An error
   */

  public CLNValidationError errorCubeNoMipmaps(
    final CLNSectionReadableImageCubeType section)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("121da0f4-d967-463d-93a3-89fc953cb427")),
      this.strings.format("errorCubeNoMipmaps"),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   *
   * @return An error
   */

  public CLNValidationError warnSectionUnaligned(
    final CLNFileSectionDescription section)
  {
    return new CLNValidationError(
      this.source,
      section.fileOffset(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("2ccedb5d-d5ec-40ba-a965-04bba40ce4ec")),
      this.strings.format(
        "warnSectionUnaligned",
        Long.toUnsignedString(section.description().identifier()),
        Long.toUnsignedString(section.fileOffset())
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   *
   * @return An error
   */

  public CLNValidationError warnEndSectionNotZeroSize(
    final CLNFileSectionDescription section)
  {
    return new CLNValidationError(
      this.source,
      section.fileOffset(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("75b25aca-58ce-4dfe-9c1b-c3140fda18e3")),
      this.strings.format(
        "warnEndSectionNotZeroSize",
        Long.toUnsignedString(section.description().size())
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @return An error
   */

  public CLNValidationError errorNoEndSection()
  {
    return new CLNValidationError(
      this.source,
      0L,
      STATUS_ERROR,
      Optional.of(UUID.fromString("a24164fd-3bdb-41fc-b04f-f7ebd4d65c4a")),
      this.strings.format("errorNoEndSection"),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   *
   * @return An error
   */

  public CLNValidationError warnArrayImageOffsetZero(
    final CLNSectionReadableImageArrayType section)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.empty(),
      this.strings.format("warnArrayImageOffsetZero"),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   *
   * @return An error
   */

  public CLNValidationError warn2DImageOffsetZero(
    final CLNSectionReadableImage2DType section)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.empty(),
      this.strings.format("warn2DImageOffsetZero"),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param octets The octets
   * @param offset The offset of the data
   *
   * @return An error
   */

  public CLNValidationError warnTrailingData(
    final long offset,
    final long octets)
  {
    return new CLNValidationError(
      this.source,
      offset,
      STATUS_WARNING,
      Optional.of(UUID.fromString("e5108d48-42fd-4de3-8137-f42aafc44e20")),
      this.strings.format("warnTrailingData", Long.toUnsignedString(octets)),
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

  public CLNValidationError errorCubeExpectedSizeZ1(
    final CLNSectionReadableImageInfoType section,
    final int sizeZ)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("21c2587a-17e5-45fb-b17f-968814d2ba17")),
      this.strings.format(
        "errorCubeExpectedSizeZ1",
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

  public CLNValidationError errorCubeMipLevelDuplicate(
    final CLNSectionReadableImageCubeType section,
    final int level)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("121da0f4-d967-463d-93a3-89fc953cb427")),
      this.strings.format(
        "errorCubeMipLevelDuplicate",
        Integer.toUnsignedString(level)
      ),
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

  public CLNValidationError errorCubeMipLevelGaps(
    final CLNSectionReadableImageCubeType section,
    final int level)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("121da0f4-d967-463d-93a3-89fc953cb427")),
      this.strings.format(
        "errorCubeMipLevelGaps",
        Integer.toUnsignedString(level)
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section The section
   * @param level   The level
   * @param face The cube face
   *
   * @return An error
   */

  public CLNValidationError errorCubeMipFaceMissing(
    final CLNSectionReadableImageCubeType section,
    final int level,
    final CLNCubeFace face)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_ERROR,
      Optional.of(UUID.fromString("121da0f4-d967-463d-93a3-89fc953cb427")),
      this.strings.format(
        "errorCubeMipFaceMissing",
        Integer.toUnsignedString(level),
        face
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param description The description
   *
   * @return An error
   */

  public CLNValidationError warnCubeUncompressedSizeZero(
    final CLNSectionReadableImageCubeType section,
    final CLNImageCubeDescription description)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("d252db29-990c-4838-acb3-f28b0d1386f6")),
      this.strings.format(
        "warnCubeUncompressedSizeZero",
        Integer.toUnsignedString(description.mipMapLevel()),
        description.face()
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param description The description
   *
   * @return An error
   */

  public CLNValidationError warnCubeCompressedSizeZero(
    final CLNSectionReadableImageCubeType section,
    final CLNImageCubeDescription description)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("db9e90ac-c9a4-40f5-b905-7126df0a9823")),
      this.strings.format(
        "warnCubeCompressedSizeZero",
        Integer.toUnsignedString(description.mipMapLevel()),
        description.face()
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   *
   * @return An error
   */

  public CLNValidationError warnCubeImageOffsetZero(
    final CLNSectionReadableImageCubeType section)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.empty(),
      this.strings.format("warnCubeImageOffsetZero"),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param description The description
   *
   * @return An error
   */

  public CLNValidationError warnCubeUncompressedDataSizeMismatch(
    final CLNSectionReadableImageCubeType section,
    final CLNImageCubeDescription description)
  {
    return new CLNValidationError(
      this.source,
      section.fileSectionDescription().fileOffsetData(),
      STATUS_WARNING,
      Optional.of(UUID.fromString("579b15a3-09bb-4b14-87ab-0441ecc88b31")),
      this.strings.format(
        "warnCubeUncompressedDataSizeMismatch",
        Long.toUnsignedString(description.dataSizeCompressed()),
        Long.toUnsignedString(description.dataSizeUncompressed()),
        Integer.toUnsignedString(description.mipMapLevel()),
        description.face()
      ),
      Optional.empty()
    );
  }

  /**
   * Construct an error.
   *
   * @param section     The section
   * @param mipMap The description
   * @param sizeReceived The received size
   *
   * @return An error
   */

  public CLNValidationError errorCubeCompressedDataSizeMismatch(
    final CLNSectionReadableImageCubeType section,
    final CLNImageCubeDescription mipMap,
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
        "errorCubeCompressedSizeMismatch",
        Integer.toUnsignedString(mipMap.mipMapLevel()),
        mipMap.face(),
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

  public CLNValidationError errorCubeUncompressedDataCRC32Mismatch(
    final CLNSectionReadableType section,
    final CLNImageCubeDescription mipMap,
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
      Optional.of(UUID.fromString("09645697-fbde-43fe-9f34-48c851adb2ff")),
      this.strings.format(
        "errorCubeUncompressedCRC32Mismatch",
        Integer.toUnsignedString(mipMap.mipMapLevel()),
        mipMap.face(),
        Integer.toUnsignedString(mipMap.crc32Uncompressed(), 16),
        Long.toUnsignedString(crc32Received, 16)
      ),
      Optional.empty()
    );
  }
}
