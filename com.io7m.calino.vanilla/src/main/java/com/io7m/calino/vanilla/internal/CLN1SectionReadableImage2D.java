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

import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.supercompression.api.CLNDecompressorFactoryType;
import com.io7m.calino.supercompression.api.CLNDecompressorRequest;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;

import java.io.IOException;
import java.nio.channels.ReadableByteChannel;
import java.nio.channels.SeekableByteChannel;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.UNCOMPRESSED;

public final class CLN1SectionReadableImage2D
  extends CLN1SectionReadableAbstract implements CLNSectionReadableImage2DType
{
  private final CLNDecompressorFactoryType decompressors;
  private CLNIOOperationType<CLNImageInfo> imageInfoRetrieval;
  private List<CLNImage2DDescription> mipMapDescriptions;
  private CLNImageInfo imageInfo;

  public CLN1SectionReadableImage2D(
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
  public List<CLNImage2DDescription> mipMapDescriptions()
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
             "image2d", 0L, sectionSize)) {

      if (subReader.bytesRemaining().orElse(0L) == 0L) {
        this.mipMapDescriptions = List.copyOf(this.mipMapDescriptions);
        return this.mipMapDescriptions;
      }

      final var mipMapCount =
        (int) (subReader.readU32BE("mipMapCount") & 0xFFFFFFFFL);

      this.checkMipMapCount(subReader, mipMapCount);

      for (var index = 0; index < mipMapCount; ++index) {
        final var mipMapLevel =
          (int) (subReader.readU32BE("mipMapLevel") & 0xFFFFFFFFL);
        final var dataOffsetWithinSection =
          subReader.readU64BE("dataOffsetWithinSection");
        final var dataSizeUncompressed =
          subReader.readU64BE("dataSizeUncompressed");
        final var dataSizeCompressed =
          subReader.readU64BE("dataSizeCompressed");
        final var crc32 =
          (int) (subReader.readU32BE("crc32") & 0xFFFFFFFFL);

        this.checkDataOffsetWithinSection(
          subReader, dataOffsetWithinSection);
        this.checkDataSizeCompressed(
          subReader, dataSizeCompressed);
        this.checkDataSizeUncompressed(
          subReader, dataSizeUncompressed);
        this.checkDataSizeCompressionMatches(
          subReader, dataSizeCompressed, dataSizeUncompressed);

        this.mipMapDescriptions.add(
          new CLNImage2DDescription(
            mipMapLevel,
            dataOffsetWithinSection,
            dataSizeUncompressed,
            dataSizeCompressed,
            crc32
          )
        );
      }
    }

    this.mipMapDescriptions = List.copyOf(this.mipMapDescriptions);
    return this.mipMapDescriptions;
  }

  private void checkDataSizeCompressionMatches(
    final BSSReaderRandomAccessType reader,
    final long dataSizeCompressed,
    final long dataSizeUncompressed)
  {
    if (this.imageInfo.superCompressionMethod() == UNCOMPRESSED) {
      if (dataSizeCompressed != dataSizeUncompressed) {
        final var request = this.request();
        request.validationReceiver().accept(
          CLNValidation.imageDataSizeCompressionSizeMismatch(
            request.source(),
            reader.offsetCurrentAbsolute(),
            dataSizeCompressed,
            dataSizeUncompressed
          )
        );
      }
    }
  }

  private void checkDataSizeUncompressed(
    final BSSReaderRandomAccessType reader,
    final long dataSizeUncompressed)
  {
    if (Long.compareUnsigned(dataSizeUncompressed, 0L) == 0) {
      final var request = this.request();
      request.validationReceiver().accept(
        CLNValidation.imageDataSizeUncompressedZero(
          request.source(),
          reader.offsetCurrentAbsolute())
      );
    }
  }

  private void checkDataSizeCompressed(
    final BSSReaderRandomAccessType reader,
    final long dataSizeCompressed)
  {
    if (Long.compareUnsigned(dataSizeCompressed, 0L) == 0) {
      final var request = this.request();
      request.validationReceiver().accept(
        CLNValidation.imageDataSizeCompressedZero(
          request.source(),
          reader.offsetCurrentAbsolute())
      );
    }
  }

  private void checkDataOffsetWithinSection(
    final BSSReaderRandomAccessType reader,
    final long dataOffsetWithinSection)
  {
    if (Long.compareUnsigned(dataOffsetWithinSection, 0L) == 0) {
      final var request = this.request();
      request.validationReceiver().accept(
        CLNValidation.imageDataOffsetWithinSectionZero(
          request.source(),
          reader.offsetCurrentAbsolute())
      );
    }
  }

  private void checkMipMapCount(
    final BSSReaderRandomAccessType reader,
    final int mipMapCount)
  {
    if (Integer.compareUnsigned(mipMapCount, 0) == 0) {
      final var request = this.request();
      request.validationReceiver().accept(
        CLNValidation.imageDataMipMapCountZero(
          request.source(),
          reader.offsetCurrentAbsolute())
      );
    }
  }

  @Override
  public ReadableByteChannel mipMapDataWithoutSupercompression(
    final CLNImage2DDescription description)
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
      new CLNCloseShieldSeekableByteChannel(baseChannel);
    final var boundedChannel =
      new CLNSubrangeReadableByteChannel(
        closeShield,
        fileSectionImageDataOffset,
        dataSize,
        context -> {

        }
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
    final CLNImage2DDescription description)
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
    final CLNImage2DDescription description)
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
    return new CLNSubrangeReadableByteChannel(
      baseChannel,
      fileSectionImageDataOffset,
      dataSize,
      (section) -> {

      }
    );
  }
}
