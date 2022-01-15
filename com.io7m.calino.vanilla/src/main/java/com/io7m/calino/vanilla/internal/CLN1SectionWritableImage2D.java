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

import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImage2DMipMapDeclaration;
import com.io7m.calino.api.CLNImage2DMipMapDeclarations;
import com.io7m.calino.api.CLNSectionWritableImage2DType;
import com.io7m.calino.api.CLNSectionWritableType;
import com.io7m.calino.api.CLWritableMipMapsType;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.nio.channels.WritableByteChannel;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;

import static java.lang.Integer.toUnsignedLong;

/**
 * A writable 2D image section.
 */

public final class CLN1SectionWritableImage2D
  extends CLN1SectionWritableAbstract
  implements CLNSectionWritableImage2DType
{
  private final BSSWriterProviderType writers;

  /**
   * A writable 2D image section.
   *
   * @param inWriters    A writer provider
   * @param inOnClose    A function executed on closing
   * @param inRequest    A write request
   * @param inIdentifier An identifier
   * @param inWriter     A writer
   */

  public CLN1SectionWritableImage2D(
    final BSSWriterProviderType inWriters,
    final BSSWriterRandomAccessType inWriter,
    final CLNWriteRequest inRequest,
    final long inIdentifier,
    final CLNOnCloseOperationType<CLNSectionWritableType> inOnClose)
  {
    super(inWriter, inRequest, inIdentifier, inOnClose);
    this.writers = Objects.requireNonNull(inWriters, "inWriters");
  }

  @Override
  public CLWritableMipMapsType createMipMaps(
    final CLNImage2DMipMapDeclarations mipMapCreate)
    throws IOException
  {
    Objects.requireNonNull(mipMapCreate, "mipMaps");

    final var mipMapsOriginal =
      mipMapCreate.mipMaps();
    final var mipMaps =
      new ArrayList<>(mipMapsOriginal);
    final var descriptions =
      new ArrayList<CLNImage2DDescription>(mipMapsOriginal.size());
    final var mipMapComparator =
      (Comparator<CLNImage2DMipMapDeclaration>) (o1, o2) -> {
        return Integer.compareUnsigned(o1.mipMapLevel(), o2.mipMapLevel());
      };

    mipMaps.sort(mipMapComparator.reversed());

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "image2D")) {

        writer.writeU32BE(toUnsignedLong(mipMaps.size()));

        for (final var mipMap : mipMaps) {
          writer.writeU32BE(toUnsignedLong(mipMap.mipMapLevel()));
          writer.writeU64BE(0L);
          writer.writeU64BE(mipMap.sizeUncompressed());
          writer.writeU64BE(mipMap.sizeCompressed());
          writer.writeU32BE(toUnsignedLong(mipMap.crc32()));
        }

        writer.align(mipMapCreate.texelBlockAlignment());

        for (final var mipMap : mipMaps) {
          writer.writeU8(0);
          writer.seekTo(writer.offsetCurrentRelative() - 1L);

          descriptions.add(
            new CLNImage2DDescription(
              mipMap.mipMapLevel(),
              writer.offsetCurrentRelative(),
              mipMap.sizeUncompressed(),
              mipMap.sizeCompressed(),
              mipMap.crc32()
            )
          );
          writer.skip(mipMap.sizeCompressed());
          writer.align(mipMapCreate.texelBlockAlignment());
          writer.seekTo(writer.offsetCurrentRelative() - 1L);
          writer.writeU8(0);
        }

        writer.seekTo(4L);

        for (final var description : descriptions) {
          writer.writeU32BE(toUnsignedLong(description.mipMapLevel()));
          writer.writeU64BE(description.dataOffsetWithinSection());
          writer.writeU64BE(description.dataSizeUncompressed());
          writer.writeU64BE(description.dataSizeCompressed());
          writer.writeU32BE(toUnsignedLong(description.crc32Uncompressed()));
        }
      }
    }

    return new MipMaps(
      this.request().channel(),
      this.offsetStartData(),
      descriptions
    );
  }

  private static final class MipMaps implements CLWritableMipMapsType
  {
    private final SeekableByteChannel fileChannel;
    private final long fileSectionDataStart;
    private final List<CLNImage2DDescription> descriptions;

    MipMaps(
      final SeekableByteChannel inChannel,
      final long inFileSectionDataStart,
      final List<CLNImage2DDescription> inDescriptions)
    {
      this.fileChannel =
        Objects.requireNonNull(inChannel, "channel");
      this.fileSectionDataStart =
        inFileSectionDataStart;
      this.descriptions =
        Objects.requireNonNull(inDescriptions, "descriptions");
    }

    @Override
    public WritableByteChannel writeMipMap(
      final int mipMapLevel)
      throws IOException
    {
      for (final var description : this.descriptions) {
        if (description.mipMapLevel() == mipMapLevel) {
          final var offset =
            this.fileSectionDataStart + description.dataOffsetWithinSection();

          this.fileChannel.position(offset);
          return new CLNSubrangeWritableByteChannel(
            this.fileChannel,
            offset,
            description.dataSizeCompressed(),
            context -> {

            }
          );
        }
      }

      throw new IllegalArgumentException(
        "No such mipmap with level " + mipMapLevel);
    }
  }
}
