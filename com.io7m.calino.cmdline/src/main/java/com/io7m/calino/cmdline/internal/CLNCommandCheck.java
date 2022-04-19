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

package com.io7m.calino.cmdline.internal;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.api.CLNSectionReadableImageArrayType;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableMetadataType;
import com.io7m.claypot.core.CLPCommandContextType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.channels.Channels;
import java.util.List;
import java.util.Optional;
import java.util.zip.CRC32;

import static com.io7m.claypot.core.CLPCommandType.Status.FAILURE;
import static com.io7m.claypot.core.CLPCommandType.Status.SUCCESS;
import static java.lang.Integer.toUnsignedLong;

/**
 * The 'check' command.
 */

@Parameters(commandDescription = "Check a texture file.")
public final class CLNCommandCheck extends CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandCheck.class);

  @Parameter(
    description = "Treat validation warnings as errors",
    arity = 1,
    required = false,
    names = "--warnings-as-errors")
  private boolean warningsAsErrors;

  private boolean processedImageData;

  /**
   * The 'check' command.
   *
   * @param inContext The context
   */

  public CLNCommandCheck(
    final CLPCommandContextType inContext)
  {
    super(inContext);
  }

  @Override
  public String extendedHelp()
  {
    return this.calinoStrings().format("cmd.check.helpExt");
  }

  @Override
  protected Status executeWithReadFile(
    final CLNFileReadableType fileParsed)
  {
    fileParsed.openImageInfo()
      .flatMap(this::checkSectionImageInfo);
    fileParsed.openImage2D()
      .ifPresent(this::checkImage2D);
    fileParsed.openImageArray()
      .ifPresent(this::checkImageArray);
    fileParsed.openMetadata()
      .ifPresent(this::checkMetadata);

    if (!this.processedImageData) {
      LOG.error("file does not contain any image data");
      this.incrementValidationErrors();
    }

    if (this.validationErrors() > 0) {
      return FAILURE;
    }

    if (this.warningsAsErrors) {
      if (this.validationWarnings() > 0) {
        LOG.info("treating warnings as errors");
        return FAILURE;
      }
    }

    return SUCCESS;
  }

  private void checkImageArray(
    final CLNSectionReadableImageArrayType sectionArray)
  {
    this.processedImageData = true;

    final List<CLNImageArrayDescription> descriptions;

    try {
      descriptions = sectionArray.mipMapDescriptions();
      LOG.info("opened image array mipmap descriptions successfully");
    } catch (final IOException e) {
      LOG.error("error opening image 2D: {}", e.getMessage());
      this.incrementValidationErrors();
      return;
    }

    for (final var description : descriptions) {
      try {
        final var channel =
          sectionArray.mipMapDataRaw(description);
        final var stream =
          Channels.newInputStream(channel);
        final var data =
          stream.readAllBytes();

        final var received = toUnsignedLong(data.length);
        final var expected = description.dataSizeCompressed();
        if (received != expected) {
          LOG.error(
            "expected {} octets of compressed data, but received {}",
            Long.toUnsignedString(expected),
            Long.toUnsignedString(received)
          );
          this.incrementValidationErrors();
          continue;
        }

        LOG.info(
          "read compressed image array mipmap [{}] data successfully",
          description.mipMapLevel()
        );
      } catch (final IOException e) {
        LOG.error("error reading compressed mipmap data: {}", e.getMessage());
        this.incrementValidationErrors();
        return;
      }
    }

    this.decompressAllMipMapsArray(sectionArray, descriptions);
  }

  private void decompressAllMipMapsArray(
    final CLNSectionReadableImageArrayType sectionArray,
    final List<CLNImageArrayDescription> descriptions)
  {
    for (final var description : descriptions) {
      try {
        try (var channel =
               sectionArray.mipMapDataWithoutSupercompression(description)) {
          final var stream =
            Channels.newInputStream(channel);
          final var data =
            stream.readAllBytes();

          final var received = toUnsignedLong(data.length);
          final var expected = description.dataSizeUncompressed();
          if (received != expected) {
            LOG.error(
              "expected {} octets of decompressed data, but received {}",
              Long.toUnsignedString(expected),
              Long.toUnsignedString(received)
            );
            this.incrementValidationErrors();
            continue;
          }

          final var crc32 = new CRC32();
          crc32.update(data);
          final var crc32Received =
            crc32.getValue() & 0xffff_ffffL;
          final var crc32Expected =
            toUnsignedLong(description.crc32Uncompressed());

          if (crc32Expected != crc32Received) {
            LOG.error(
              "CRC32 checksum of mipmap [{}] did not match (expected 0x{} but received 0x{})",
              description.mipMapLevel(),
              Long.toUnsignedString(crc32Expected, 16),
              Long.toUnsignedString(crc32Received, 16)
            );
            this.incrementValidationErrors();
            continue;
          }

          LOG.info(
            "decompressed and verified image array mipmap [{}]",
            description.mipMapLevel()
          );
        }
      } catch (final IOException e) {
        LOG.error("error decompressing mipmap data: {}", e.getMessage());
        this.incrementValidationErrors();
        return;
      }
    }
  }

  private void checkMetadata(
    final CLNSectionReadableMetadataType section)
  {
    try {
      final var data = section.metadata();
      LOG.info("read {} metadata entries successfully", data.size());
    } catch (final IOException e) {
      LOG.error("error metadata: {}", e.getMessage());
      this.incrementValidationErrors();
      return;
    }
  }

  private void checkImage2D(
    final CLNSectionReadableImage2DType sectionImage2D)
  {
    this.processedImageData = true;

    final List<CLNImage2DDescription> descriptions;

    try {
      descriptions = sectionImage2D.mipMapDescriptions();
      LOG.info("opened image 2D mipmap descriptions successfully");
    } catch (final IOException e) {
      LOG.error("error opening image 2D: {}", e.getMessage());
      this.incrementValidationErrors();
      return;
    }

    for (final var description : descriptions) {
      try {
        final var channel =
          sectionImage2D.mipMapDataRaw(description);
        final var stream =
          Channels.newInputStream(channel);
        final var data =
          stream.readAllBytes();

        final var received = toUnsignedLong(data.length);
        final var expected = description.dataSizeCompressed();
        if (received != expected) {
          LOG.error(
            "expected {} octets of compressed data, but received {}",
            Long.toUnsignedString(expected),
            Long.toUnsignedString(received)
          );
          this.incrementValidationErrors();
          continue;
        }

        LOG.info(
          "read compressed image 2D mipmap [{}] data successfully",
          description.mipMapLevel()
        );
      } catch (final IOException e) {
        LOG.error("error reading compressed mipmap data: {}", e.getMessage());
        this.incrementValidationErrors();
        return;
      }
    }

    this.decompressAllMipMaps2D(sectionImage2D, descriptions);
  }

  private void decompressAllMipMaps2D(
    final CLNSectionReadableImage2DType sectionImage2D,
    final List<CLNImage2DDescription> descriptions)
  {
    for (final var description : descriptions) {
      try {
        try (var channel =
               sectionImage2D.mipMapDataWithoutSupercompression(description)) {
          final var stream =
            Channels.newInputStream(channel);
          final var data =
            stream.readAllBytes();

          final var received = toUnsignedLong(data.length);
          final var expected = description.dataSizeUncompressed();
          if (received != expected) {
            LOG.error(
              "expected {} octets of decompressed data, but received {}",
              Long.toUnsignedString(expected),
              Long.toUnsignedString(received)
            );
            this.incrementValidationErrors();
            continue;
          }

          final var crc32 = new CRC32();
          crc32.update(data);
          final var crc32Received =
            crc32.getValue() & 0xffff_ffffL;
          final var crc32Expected =
            toUnsignedLong(description.crc32Uncompressed());

          if (crc32Expected != crc32Received) {
            LOG.error(
              "CRC32 checksum of mipmap [{}] did not match (expected 0x{} but received 0x{})",
              description.mipMapLevel(),
              Long.toUnsignedString(crc32Expected, 16),
              Long.toUnsignedString(crc32Received, 16)
            );
            this.incrementValidationErrors();
            continue;
          }

          LOG.info(
            "decompressed and verified image 2D mipmap [{}]",
            description.mipMapLevel()
          );
        }
      } catch (final IOException e) {
        LOG.error("error decompressing mipmap data: {}", e.getMessage());
        this.incrementValidationErrors();
        return;
      }
    }
  }

  private Optional<CLNImageInfo> checkSectionImageInfo(
    final CLNSectionReadableImageInfoType sectionImageInfo)
  {
    try {
      return Optional.of(sectionImageInfo.info());
    } catch (final IOException e) {
      LOG.error("error opening image info: {}", e.getMessage());
      this.incrementValidationErrors();
      return Optional.empty();
    }
  }

  @Override
  public String name()
  {
    return "check";
  }
}
