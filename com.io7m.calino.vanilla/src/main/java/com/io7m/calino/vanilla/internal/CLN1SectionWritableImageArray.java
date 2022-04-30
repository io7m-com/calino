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

import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNImageArrayMipMapDeclarations;
import com.io7m.calino.api.CLNSectionWritableImageArrayType;
import com.io7m.calino.api.CLNSectionWritableType;
import com.io7m.calino.api.CLWritableMipMapsArrayType;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.wendover.core.CloseShieldSeekableByteChannel;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.nio.channels.WritableByteChannel;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static java.lang.Integer.toUnsignedLong;

/**
 * A writable array image section.
 */

public final class CLN1SectionWritableImageArray
  extends CLN1SectionWritableAbstract
  implements CLNSectionWritableImageArrayType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN1SectionWritableImageArray.class);

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

  public CLN1SectionWritableImageArray(
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
  public CLWritableMipMapsArrayType createMipMaps(
    final CLNImageArrayMipMapDeclarations mipMapCreate)
    throws IOException
  {
    Objects.requireNonNull(mipMapCreate, "mipMaps");

    final var mipMaps =
      mipMapCreate.mipMaps();
    final var descriptions =
      new ArrayList<CLNImageArrayDescription>(mipMaps.size());

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "image2D")) {

        /*
         * Write out the list of mipmap descriptions, leaving the offset
         * values unspecified.
         */

        writer.writeU32BE(toUnsignedLong(mipMaps.size()));

        for (final var mipMap : mipMaps) {
          writer.writeU32BE(toUnsignedLong(mipMap.mipMapLevel()));
          writer.writeU32BE(toUnsignedLong(mipMap.layer()));
          writer.writeU64BE(0L);
          writer.writeU64BE(mipMap.sizeUncompressed());
          writer.writeU64BE(mipMap.sizeCompressed());
          writer.writeU32BE(toUnsignedLong(mipMap.crc32()));
        }

        /*
         * Now, seek to the start of where the mipmap data would be, and
         * start calculating offset values to produce full descriptions
         * for mipmaps.
         */

        writer.align(mipMapCreate.texelBlockAlignment());

        for (final var mipMap : mipMaps) {
          writer.writeU8(0);
          writer.seekTo(writer.offsetCurrentRelative() - 1L);

          descriptions.add(
            new CLNImageArrayDescription(
              mipMap.mipMapLevel(),
              mipMap.layer(),
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

        LOG.trace(
          "array mipmaps max @ {}",
          Long.toUnsignedString(writer.offsetCurrentAbsolute())
        );

        /*
         * Now, seek back to the start of the section and write out
         * the fully updated descriptions.
         */

        writer.seekTo(4L);

        for (final var description : descriptions) {
          writer.writeU32BE(toUnsignedLong(description.mipMapLevel()));
          writer.writeU32BE(toUnsignedLong(description.layer()));
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

  private static final class MipMaps implements CLWritableMipMapsArrayType
  {
    private final SeekableByteChannel fileChannel;
    private final long fileSectionDataStart;
    private final List<CLNImageArrayDescription> descriptions;

    MipMaps(
      final SeekableByteChannel inChannel,
      final long inFileSectionDataStart,
      final List<CLNImageArrayDescription> inDescriptions)
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
      final int mipMapLevel,
      final int layer)
      throws IOException
    {
      for (final var description : this.descriptions) {
        final var matchesLevel = description.mipMapLevel() == mipMapLevel;
        final var matchesLayer = description.layer() == layer;
        if (matchesLevel && matchesLayer) {
          final var offset =
            this.fileSectionDataStart + description.dataOffsetWithinSection();

          this.fileChannel.position(offset);

          LOG.trace(
            "mipmap @ {}",
            Long.toUnsignedString(offset)
          );
          LOG.trace(
            "mipmap end approx @ {}",
            Long.toUnsignedString(offset + description.dataSizeCompressed())
          );

          final var closeShieldChannel =
            new CloseShieldSeekableByteChannel(this.fileChannel);

          return new SubrangeSeekableByteChannel(
            closeShieldChannel,
            offset,
            description.dataSizeCompressed()
          );
        }
      }

      throw new IllegalArgumentException(
        "No such mipmap with level %d and layer %d"
          .formatted(mipMapLevel, layer)
      );
    }
  }
}
