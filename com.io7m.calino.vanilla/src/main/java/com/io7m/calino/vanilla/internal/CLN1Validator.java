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

import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.api.CLNSectionReadableImageArrayType;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableMetadataType;
import com.io7m.calino.validation.api.CLNValidationError;
import com.io7m.calino.validation.api.CLNValidatorType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.channels.Channels;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.zip.CRC32;

import static java.lang.Integer.toUnsignedLong;

/**
 * A validator.
 */

public final class CLN1Validator implements CLNValidatorType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN1Validator.class);

  private final CLNFileReadableType file;
  private List<CLNValidationError> errors;
  private boolean processedImageData;
  private final CLN1ValidationErrors errorFactory;

  /**
   * A validator.
   *
   * @param inErrors An error factory
   * @param inFile   The file to be validated
   */

  public CLN1Validator(
    final CLN1ValidationErrors inErrors,
    final CLNFileReadableType inFile)
  {
    this.file =
      Objects.requireNonNull(inFile, "file");
    this.errorFactory =
      Objects.requireNonNull(inErrors, "errors");
  }

  @Override
  public List<CLNValidationError> execute()
  {
    this.errors = new ArrayList<>();

    final var infoSectionOpt =
      this.file.openImageInfo();

    if (infoSectionOpt.isEmpty()) {
      this.publishError(this.errorFactory.errorImageInfoNotPresent());
      return this.errors;
    }

    final var infoSection =
      infoSectionOpt.get();

    final var imageInfoOpt =
      this.checkSectionImageInfo(infoSection);

    if (imageInfoOpt.isEmpty()) {
      return this.errors;
    }

    final var imageInfo =
      imageInfoOpt.get();

    this.file.openImage2D()
      .ifPresent(image2D -> this.checkImage2D(imageInfo, image2D));
    this.file.openImageArray()
      .ifPresent(imageArray -> this.checkImageArray(imageInfo, imageArray));
    this.file.openMetadata()
      .ifPresent(this::checkMetadata);

    if (!this.processedImageData) {
      this.publishError(this.errorFactory.errorImageDataNotPresent());
    }

    return this.errors;
  }

  private void checkImage2D(
    final ImageInfoParsed imageInfo,
    final CLNSectionReadableImage2DType section)
  {
    this.processedImageData = true;

    final var sizeZ = imageInfo.imageInfo.sizeZ();
    if (sizeZ != 1) {
      final var infoSection = imageInfo.section;
      this.publishError(this.errorFactory.error2DExpectedSizeZ1(
        infoSection,
        sizeZ));
    }

    final List<CLNImage2DDescription> descriptions;

    try {
      descriptions = section.mipMapDescriptions();
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        section, e, "Failed to parse 2D image mipmaps"));
      return;
    }

    this.check2DMipMapWellOrdered(section, descriptions);
    this.check2DMipMapCompressedDataAll(section, descriptions);
  }

  private void check2DMipMapWellOrdered(
    final CLNSectionReadableImage2DType section,
    final List<CLNImage2DDescription> descriptions)
  {
    final var mipLevelSet = new HashSet<Integer>(descriptions.size());
    var mipHighest = 0;
    for (final var mipMap : descriptions) {
      final var level = mipMap.mipMapLevel();
      if (mipLevelSet.contains(level)) {
        this.publishError(
          this.errorFactory.error2DMipLevelDuplicate(section, level)
        );
      }
      mipLevelSet.add(level);
      mipHighest = Math.max(mipHighest, level);
    }

    for (int mipLevel = 0; mipLevel <= mipHighest; ++mipLevel) {
      if (!mipLevelSet.contains(mipLevel)) {
        this.publishError(
          this.errorFactory.error2DMipLevelGaps(section, mipHighest)
        );
      }
    }

    final var sorted =
      descriptions.stream()
        .sorted()
        .toList();

    if (!Objects.equals(sorted, descriptions)) {
      this.publishError(
        this.errorFactory.error2DMipLevelGaps(section, mipHighest)
      );
    }
  }

  private void check2DMipMapCompressedDataAll(
    final CLNSectionReadableImage2DType section,
    final List<CLNImage2DDescription> descriptions)
  {
    for (final var description : descriptions) {
      this.check2DMipMapCompressedDataOne(section, description);
    }
  }

  private void check2DMipMapCompressedDataOne(
    final CLNSectionReadableImage2DType section,
    final CLNImage2DDescription description)
  {
    try (var channel =
           section.mipMapDataWithoutSupercompression(description)) {
      final var stream =
        Channels.newInputStream(channel);
      final var data =
        stream.readAllBytes();

      final var received = toUnsignedLong(data.length);
      final var expected = description.dataSizeUncompressed();
      if (received != expected) {
        this.publishError(this.errorFactory.error2DCompressedDataSizeMismatch(
          section,
          description,
          received
        ));
        return;
      }

      final var crc32 = new CRC32();
      crc32.update(data);
      final var crc32Received =
        crc32.getValue() & 0xffff_ffffL;
      final var crc32Expected =
        toUnsignedLong(description.crc32Uncompressed());

      if (crc32Expected != crc32Received) {
        this.publishError(this.errorFactory.error2DUncompressedDataCRC32Mismatch(
          section,
          description,
          crc32Received
        ));
      }
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        section, e, "I/O error reading compressed mipmap data"));
    }
  }

  private boolean publishError(
    final CLNValidationError error)
  {
    LOG.debug("{}", error.message());
    return this.errors.add(error);
  }

  private record ImageInfoParsed(
    CLNSectionReadableImageInfoType section,
    CLNImageInfo imageInfo)
  {

  }

  private Optional<ImageInfoParsed> checkSectionImageInfo(
    final CLNSectionReadableImageInfoType sectionImageInfo)
  {
    try {
      return Optional.of(new ImageInfoParsed(
        sectionImageInfo,
        sectionImageInfo.info()
      ));
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        sectionImageInfo, e, "Failed to read image info section"));
      return Optional.empty();
    }
  }

  private void checkImageArray(
    final ImageInfoParsed imageInfo,
    final CLNSectionReadableImageArrayType section)
  {
    this.processedImageData = true;

    final List<CLNImageArrayDescription> descriptions;

    try {
      descriptions = section.mipMapDescriptions();
      LOG.info("opened image array mipmap descriptions successfully");
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        section, e, "Failed to parse array image mipmaps"));
      return;
    }

    this.checkArrayMipMapWellOrdered(
      section,
      imageInfo.imageInfo.sizeZ(),
      descriptions);
    this.checkArrayMipMapCompressedDataAll(section, descriptions);
  }

  private void checkArrayMipMapWellOrdered(
    final CLNSectionReadableImageArrayType section,
    final int expectedLayerCount,
    final List<CLNImageArrayDescription> descriptions)
  {
    final var mips =
      new HashMap<Integer, Map<Integer, CLNImageArrayDescription>>(
        descriptions.size());

    var mipHighest = 0;
    var layerHighest = 0;

    for (final var mipMap : descriptions) {
      final var level = mipMap.mipMapLevel();
      final var layer = mipMap.layer();

      var layers = mips.get(level);
      if (layers == null) {
        layers = new HashMap<>();
      }
      if (layers.containsKey(layer)) {
        this.publishError(
          this.errorFactory.errorArrayMipNotUnique(section, level, layer)
        );
      }

      layers.put(layer, mipMap);
      mips.put(level, layers);
      mipHighest = Math.max(mipHighest, level);
      layerHighest = Math.max(layerHighest, layer);
    }

    for (int mipLevel = 0; mipLevel <= mipHighest; ++mipLevel) {
      final var layers = mips.get(mipLevel);
      if (layers == null) {
        this.publishError(
          this.errorFactory.errorArrayMipLevelGaps(section, mipHighest)
        );
        continue;
      }

      for (int layer = 0; layer <= layerHighest; ++layer) {
        if (!layers.containsKey(layer)) {
          this.publishError(
            this.errorFactory.errorArrayMipLayerGaps(
              section,
              mipLevel,
              layerHighest,
              layers.keySet())
          );
        }
      }
    }

    final var receivedLayerCount = layerHighest + 1;
    if (receivedLayerCount != expectedLayerCount) {
      this.publishError(
        this.errorFactory.errorArrayLayerCount(
          section,
          expectedLayerCount,
          receivedLayerCount)
      );
    }

    final var sorted =
      descriptions.stream()
        .sorted()
        .toList();

    if (!Objects.equals(sorted, descriptions)) {
      this.publishError(
        this.errorFactory.errorArrayMipLevelGaps(section, mipHighest)
      );
    }
  }

  private void checkArrayMipMapCompressedDataAll(
    final CLNSectionReadableImageArrayType section,
    final List<CLNImageArrayDescription> descriptions)
  {
    for (final var description : descriptions) {
      this.checkArrayMipMapCompressedDataOne(section, description);
    }
  }

  private void checkArrayMipMapCompressedDataOne(
    final CLNSectionReadableImageArrayType section,
    final CLNImageArrayDescription description)
  {
    try (var channel =
           section.mipMapDataWithoutSupercompression(description)) {
      final var stream =
        Channels.newInputStream(channel);
      final var data =
        stream.readAllBytes();

      final var received = toUnsignedLong(data.length);
      final var expected = description.dataSizeUncompressed();
      if (received != expected) {
        this.publishError(this.errorFactory.errorArrayCompressedDataSizeMismatch(
          section,
          description,
          received
        ));
        return;
      }

      final var crc32 = new CRC32();
      crc32.update(data);
      final var crc32Received =
        crc32.getValue() & 0xffff_ffffL;
      final var crc32Expected =
        toUnsignedLong(description.crc32Uncompressed());

      if (crc32Expected != crc32Received) {
        this.publishError(this.errorFactory.errorArrayUncompressedDataCRC32Mismatch(
          section,
          description,
          crc32Received
        ));
      }
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        section, e, "I/O error reading compressed mipmap data"));
    }
  }

  private void checkMetadata(
    final CLNSectionReadableMetadataType section)
  {
    try {
      section.metadata();
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        section, e, "I/O error reading metadata values"));
    }
  }
}
