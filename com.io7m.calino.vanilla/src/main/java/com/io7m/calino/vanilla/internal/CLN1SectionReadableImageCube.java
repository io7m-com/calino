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

package com.io7m.calino.vanilla.internal;

import com.io7m.calino.api.CLNCubeFace;
import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNImageCubeDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImageCubeType;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.supercompression.api.CLNDecompressorFactoryType;
import com.io7m.calino.supercompression.api.CLNDecompressorRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;
import com.io7m.wendover.core.CloseShieldSeekableByteChannel;
import com.io7m.wendover.core.ReadOnlySeekableByteChannel;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.ReadableByteChannel;
import java.nio.channels.SeekableByteChannel;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.UNCOMPRESSED;

/**
 * A readable cube image section.
 */

public final class CLN1SectionReadableImageCube
  extends CLN1SectionReadableAbstract implements CLNSectionReadableImageCubeType
{
  private final CLNDecompressorFactoryType decompressors;
  private final CLNIOOperationType<CLNImageInfo> imageInfoRetrieval;
  private List<CLNImageCubeDescription> mipMapDescriptions;
  private CLNImageInfo imageInfo;

  /**
   * A readable 2D image section.
   *
   * @param inDescription        The description
   * @param inReader             The reader
   * @param inRequest            The request
   * @param inDecompressors      The decompressors
   * @param inImageInfoRetrieval A function to retrieve image information
   */

  CLN1SectionReadableImageCube(
    final CLNDecompressorFactoryType inDecompressors,
    final BSSReaderRandomAccessType inReader,
    final CLNParseRequest inRequest,
    final CLNFileSectionDescription inDescription,
    final CLNIOOperationType<CLNImageInfo> inImageInfoRetrieval)
  {
    super(inReader, inRequest, inDescription);

    this.decompressors =
      Objects.requireNonNull(inDecompressors, "decompressors");
    this.imageInfoRetrieval =
      Objects.requireNonNull(inImageInfoRetrieval, "imageInfoRetrieval");
  }

  @Override
  public List<CLNImageCubeDescription> mipMapDescriptions()
    throws IOException
  {
    if (this.imageInfo == null) {
      this.imageInfo = this.imageInfoRetrieval.execute();
    }

    if (this.mipMapDescriptions != null) {
      return this.mipMapDescriptions;
    }

    final var reader =
      this.reader();
    final var fileOffset =
      this.fileSectionDescription().fileOffset();
    final var sectionSize =
      this.description().size();

    reader.seekTo(fileOffset);
    reader.skip(16L);

    this.mipMapDescriptions = new ArrayList<>();
    try (var subReader =
           reader.createSubReaderAtBounded(
             "imageCube", 0L, sectionSize)) {

      if (subReader.bytesRemaining().orElse(0L) == 0L) {
        this.mipMapDescriptions = List.copyOf(this.mipMapDescriptions);
        return this.mipMapDescriptions;
      }

      final var mipMapCount =
        (int) (subReader.readU32BE("mipMapCount") & 0xFFFFFFFFL);

      final var facesOrdered =
        CLNCubeFace.facesInOrder();

      for (var index = 0; index < mipMapCount; ++index) {
        final var mipMapLevel =
          (int) (subReader.readU32BE("mipMapLevel") & 0xFFFFFFFFL);

        for (final var face : facesOrdered) {
          final var dataOffsetWithinSection =
            subReader.readU64BE("dataOffsetWithinSection");
          final var dataSizeUncompressed =
            subReader.readU64BE("dataSizeUncompressed");
          final var dataSizeCompressed =
            subReader.readU64BE("dataSizeCompressed");
          final var crc32 =
            (int) (subReader.readU32BE("crc32") & 0xFFFFFFFFL);

          this.mipMapDescriptions.add(
            new CLNImageCubeDescription(
              mipMapLevel,
              face,
              dataOffsetWithinSection,
              dataSizeUncompressed,
              dataSizeCompressed,
              crc32
            )
          );
        }
      }
    }

    this.mipMapDescriptions = List.copyOf(this.mipMapDescriptions);
    return this.mipMapDescriptions;
  }

  @Override
  public ReadableByteChannel mipMapDataWithoutSupercompression(
    final CLNImageCubeDescription description)
    throws IOException
  {
    final var descriptions =
      this.mipMapDescriptions();

    if (!descriptions.contains(description)) {
      throw new IllegalArgumentException(
        "An image with the given description is not present");
    }

    if (this.imageInfo.superCompressionMethod() == UNCOMPRESSED) {
      return this.mipMapDataRaw(description);
    }

    /*
     * Create a bounded, uncloseable byte channel that provides a view into the
     * compressed data. This is passed to the decompressor factory
     * that can decompress the data if appropriate support is available.
     */

    final var fileSectionImageDataOffset =
      this.determineFileSectionImageDataOffset(description);
    final var dataSize =
      description.dataSizeCompressed();
    final var baseChannel =
      this.request().channel();

    baseChannel.position(fileSectionImageDataOffset);

    final var closeShield =
      new CloseShieldSeekableByteChannel(baseChannel);
    final var readOnlyChannel =
      new ReadOnlySeekableByteChannel(closeShield);
    final var boundedChannel =
      new SubrangeSeekableByteChannel(
        readOnlyChannel,
        fileSectionImageDataOffset,
        dataSize
      );

    return this.decompressors.createDecompressor(
      new CLNDecompressorRequest(
        this.imageInfo.superCompressionMethod(),
        description,
        boundedChannel
      )
    ).decompressedData();
  }

  private long determineFileSectionImageDataOffset(
    final CLNImageCubeDescription description)
  {
    final var fileSectionOffset =
      this.fileSectionDescription()
        .fileOffset();
    final var fileSectionDataOffset =
      fileSectionOffset + 16L;
    return fileSectionDataOffset + description.dataOffsetWithinSection();
  }

  @Override
  public SeekableByteChannel mipMapDataRaw(
    final CLNImageCubeDescription description)
    throws IOException
  {
    final var descriptions =
      this.mipMapDescriptions();

    if (!descriptions.contains(description)) {
      throw new IllegalArgumentException(
        "An image with the given description is not present");
    }

    final var fileSectionImageDataOffset =
      this.determineFileSectionImageDataOffset(description);
    final var dataSize =
      description.dataSizeCompressed();
    final var baseChannel =
      this.request().channel();

    baseChannel.position(fileSectionImageDataOffset);

    final var closeShield =
      new CloseShieldSeekableByteChannel(baseChannel);
    final var readOnlyChannel =
      new ReadOnlySeekableByteChannel(closeShield);

    return new SubrangeSeekableByteChannel(
      readOnlyChannel,
      fileSectionImageDataOffset,
      dataSize
    );
  }
}
