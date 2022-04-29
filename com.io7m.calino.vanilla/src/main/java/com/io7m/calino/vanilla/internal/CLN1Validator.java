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
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNImageCubeDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableEndType;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.api.CLNSectionReadableImageArrayType;
import com.io7m.calino.api.CLNSectionReadableImageCubeType;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableMetadataType;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.calino.validation.api.CLNValidationError;
import com.io7m.calino.validation.api.CLNValidatorType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.channels.Channels;
import java.util.ArrayList;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.zip.CRC32;

import static com.io7m.calino.api.CLNCubeFace.facesInOrder;
import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.UNCOMPRESSED;
import static java.lang.Integer.toUnsignedLong;
import static java.lang.Math.max;

/**
 * A validator.
 */

public final class CLN1Validator implements CLNValidatorType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN1Validator.class);

  private final CLNFileReadableType file;
  private final CLN1ValidationErrors errorFactory;
  private List<CLNValidationError> errors;
  private boolean processedImageData;

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

    for (final var section : this.file.sections()) {
      this.checkSectionAlignment(section);
    }

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
    this.file.openImageCube()
      .ifPresent(imageCube -> this.checkImageCube(imageInfo, imageCube));

    this.file.openMetadata()
      .ifPresent(this::checkMetadata);
    this.file.openEnd()
      .ifPresentOrElse(this::checkEnd, () -> {
        this.publishError(this.errorFactory.errorNoEndSection());
      });

    if (!this.processedImageData) {
      this.publishError(this.errorFactory.errorImageDataNotPresent());
    }

    if (this.file.trailingOctets() != 0L) {
      this.publishError(
        this.errorFactory.warnTrailingData(0L, this.file.trailingOctets()
        ));
    }

    return this.errors;
  }

  private void checkEnd(
    final CLNSectionReadableEndType section)
  {
    if (section.description().size() != 0L) {
      this.publishError(this.errorFactory.warnEndSectionNotZeroSize(
        section.fileSectionDescription()));
    }
  }

  private void checkSectionAlignment(
    final CLNFileSectionDescription section)
  {
    if (section.fileOffset() % 16L != 0L) {
      this.publishError(this.errorFactory.warnSectionUnaligned(section));
    }
  }

  private void checkImageCube(
    final ImageInfoParsed imageInfo,
    final CLNSectionReadableImageCubeType section)
  {
    this.processedImageData = true;

    final var sizeZ = imageInfo.imageInfo.sizeZ();
    if (sizeZ != 1) {
      final var infoSection = imageInfo.section;
      this.publishError(this.errorFactory.errorCubeExpectedSizeZ1(
        infoSection,
        sizeZ));
    }

    final List<CLNImageCubeDescription> descriptions;

    try {
      descriptions = section.mipMapDescriptions();
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        section, e, "Failed to parse cube image mipmaps"));
      return;
    }

    if (descriptions.isEmpty()) {
      this.publishError(this.errorFactory.errorCubeNoMipmaps(section));
      return;
    }

    this.checkCubeMipMapWellOrdered(section, descriptions);
    this.checkCubeMipMapCompressedDataAll(
      section,
      imageInfo.imageInfo.superCompressionMethod(),
      descriptions
    );
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

    if (descriptions.isEmpty()) {
      this.publishError(this.errorFactory.error2DNoMipmaps(section));
      return;
    }

    this.check2DMipMapWellOrdered(section, descriptions);
    this.check2DMipMapCompressedDataAll(
      section,
      imageInfo.imageInfo.superCompressionMethod(),
      descriptions
    );
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
      mipHighest = max(mipHighest, level);
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

  private void checkCubeMipMapWellOrdered(
    final CLNSectionReadableImageCubeType section,
    final List<CLNImageCubeDescription> descriptions)
  {
    final var facesByLevel =
      new HashMap<Integer, EnumMap<CLNCubeFace, CLNImageCubeDescription>>();

    var mipHighest = 0;
    for (final var mipMap : descriptions) {
      final var level =
        mipMap.mipMapLevel();

      mipHighest = max(level, mipHighest);

      var byFace =
        facesByLevel.get(Integer.valueOf(level));

      if (byFace == null) {
        byFace = new EnumMap<>(CLNCubeFace.class);
      }

      byFace.put(mipMap.face(), mipMap);
      facesByLevel.put(Integer.valueOf(level), byFace);
    }

    for (int mipLevel = 0; mipLevel <= mipHighest; ++mipLevel) {
      final var byFace =
        facesByLevel.get(Integer.valueOf(mipLevel));

      if (byFace == null) {
        this.publishError(
          this.errorFactory.errorCubeMipLevelGaps(section, mipHighest)
        );
        continue;
      }

      for (final var face : facesInOrder()) {
        if (!byFace.containsKey(face)) {
          this.publishError(
            this.errorFactory.errorCubeMipFaceMissing(section, mipLevel, face)
          );
        }
      }
    }

    final var sorted =
      descriptions.stream()
        .sorted()
        .toList();

    if (!Objects.equals(sorted, descriptions)) {
      this.publishError(
        this.errorFactory.errorCubeMipLevelGaps(section, mipHighest)
      );
    }
  }

  private void checkCubeMipMapCompressedDataAll(
    final CLNSectionReadableImageCubeType section,
    final CLNSuperCompressionMethodType superCompression,
    final List<CLNImageCubeDescription> descriptions)
  {
    for (final var description : descriptions) {
      this.checkCubeMipMapCompressedDataOne(
        section,
        superCompression,
        description);
    }
  }

  private void checkCubeMipMapCompressedDataOne(
    final CLNSectionReadableImageCubeType section,
    final CLNSuperCompressionMethodType superCompression,
    final CLNImageCubeDescription description)
  {
    if (description.dataSizeUncompressed() == 0L) {
      this.publishError(
        this.errorFactory.warnCubeUncompressedSizeZero(section, description)
      );
    }

    if (description.dataSizeCompressed() == 0L) {
      this.publishError(
        this.errorFactory.warnCubeCompressedSizeZero(section, description)
      );
    }

    if (description.dataOffsetWithinSection() == 0L) {
      this.publishError(
        this.errorFactory.warnCubeImageOffsetZero(section)
      );
    }

    if (superCompression == UNCOMPRESSED) {
      if (description.dataSizeCompressed() != description.dataSizeUncompressed()) {
        this.publishError(
          this.errorFactory.warnCubeUncompressedDataSizeMismatch(
            section, description)
        );
      }
    }

    try (var channel =
           section.mipMapDataWithoutSupercompression(description)) {
      final var stream =
        Channels.newInputStream(channel);
      final var data =
        stream.readAllBytes();

      final var received = toUnsignedLong(data.length);
      final var expected = description.dataSizeUncompressed();
      if (received != expected) {
        this.publishError(this.errorFactory.errorCubeCompressedDataSizeMismatch(
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

      if (crc32Expected != 0L) {
        if (crc32Expected != crc32Received) {
          this.publishError(this.errorFactory.errorCubeUncompressedDataCRC32Mismatch(
            section,
            description,
            crc32Received
          ));
        }
      }
    } catch (final IOException e) {
      this.publishError(this.errorFactory.errorOfException(
        section, e, "I/O error reading compressed mipmap data"));
    }
  }

  private void check2DMipMapCompressedDataAll(
    final CLNSectionReadableImage2DType section,
    final CLNSuperCompressionMethodType superCompression,
    final List<CLNImage2DDescription> descriptions)
  {
    for (final var description : descriptions) {
      this.check2DMipMapCompressedDataOne(
        section,
        superCompression,
        description);
    }
  }

  private void check2DMipMapCompressedDataOne(
    final CLNSectionReadableImage2DType section,
    final CLNSuperCompressionMethodType superCompression,
    final CLNImage2DDescription description)
  {
    if (description.dataSizeUncompressed() == 0L) {
      this.publishError(
        this.errorFactory.warn2DUncompressedSizeZero(section, description)
      );
    }

    if (description.dataSizeCompressed() == 0L) {
      this.publishError(
        this.errorFactory.warn2DCompressedSizeZero(section, description)
      );
    }

    if (description.dataOffsetWithinSection() == 0L) {
      this.publishError(
        this.errorFactory.warn2DImageOffsetZero(section)
      );
    }

    if (superCompression == UNCOMPRESSED) {
      if (description.dataSizeCompressed() != description.dataSizeUncompressed()) {
        this.publishError(
          this.errorFactory.warn2DUncompressedDataSizeMismatch(
            section, description)
        );
      }
    }

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

      if (crc32Expected != 0L) {
        if (crc32Expected != crc32Received) {
          this.publishError(this.errorFactory.error2DUncompressedDataCRC32Mismatch(
            section,
            description,
            crc32Received
          ));
        }
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

    if (descriptions.isEmpty()) {
      this.publishError(this.errorFactory.errorArrayNoMipmaps(section));
      return;
    }

    this.checkArrayMipMapWellOrdered(
      section,
      imageInfo.imageInfo.sizeZ(),
      descriptions
    );

    this.checkArrayMipMapCompressedDataAll(
      section,
      imageInfo.imageInfo.superCompressionMethod(),
      descriptions
    );
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
      mipHighest = max(mipHighest, level);
      layerHighest = max(layerHighest, layer);
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
    final CLNSuperCompressionMethodType superCompression,
    final List<CLNImageArrayDescription> descriptions)
  {
    for (final var description : descriptions) {
      this.checkArrayMipMapCompressedDataOne(
        section, superCompression, description);
    }
  }

  private void checkArrayMipMapCompressedDataOne(
    final CLNSectionReadableImageArrayType section,
    final CLNSuperCompressionMethodType superCompression,
    final CLNImageArrayDescription description)
  {
    if (description.dataSizeUncompressed() == 0L) {
      this.publishError(
        this.errorFactory.warnArrayUncompressedSizeZero(section, description)
      );
    }

    if (description.dataSizeCompressed() == 0L) {
      this.publishError(
        this.errorFactory.warnArrayCompressedSizeZero(section, description)
      );
    }

    if (description.dataOffsetWithinSection() == 0L) {
      this.publishError(
        this.errorFactory.warnArrayImageOffsetZero(section)
      );
    }

    if (superCompression == UNCOMPRESSED) {
      if (description.dataSizeCompressed() != description.dataSizeUncompressed()) {
        this.publishError(
          this.errorFactory.warnArrayUncompressedDataSizeMismatch(
            section,
            description)
        );
      }
    }

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

      if (crc32Expected != 0L) {
        if (crc32Expected != crc32Received) {
          this.publishError(this.errorFactory.errorArrayUncompressedDataCRC32Mismatch(
            section,
            description,
            crc32Received
          ));
        }
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

  private record ImageInfoParsed(
    CLNSectionReadableImageInfoType section,
    CLNImageInfo imageInfo)
  {

  }
}
