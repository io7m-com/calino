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

import com.io7m.calino.api.CLNException;
import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNImageArrayMipMapDeclarations;
import com.io7m.calino.api.CLNSectionWritableImageArrayType;
import com.io7m.calino.api.CLWritableMipMapsArrayType;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;
import com.io7m.wendover.core.UncloseableSeekableByteChannel;
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
 * A writable image array section.
 */

final class CLN2SectionWritableImageArray
  extends CLN2SectionWritableAbstract
  implements CLNSectionWritableImageArrayType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN2SectionWritableImageArray.class);

  CLN2SectionWritableImageArray(
    final CloseableCollectionType<CLNException> resources,
    final CLNOnCloseOperationType<CLN2SectionWritableAbstract> inOnClose)
    throws IOException
  {
    super(CLNIdentifiers.sectionImageArrayIdentifier(), resources, inOnClose);
  }

  @Override
  public CLWritableMipMapsArrayType createMipMaps(
    final CLNImageArrayMipMapDeclarations mipMapCreate)
    throws IOException
  {
    final var mipMaps =
      mipMapCreate.mipMaps();
    final var descriptions =
      new ArrayList<CLNImageArrayDescription>(mipMaps.size());

    final var writer = this.writer();

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

    return new MipMaps(
      this.sectionDataChannel(),
      descriptions
    );
  }

  private static final class MipMaps
    implements CLWritableMipMapsArrayType
  {
    private final SeekableByteChannel fileChannel;
    private final List<CLNImageArrayDescription> descriptions;

    MipMaps(
      final SeekableByteChannel inChannel,
      final List<CLNImageArrayDescription> inDescriptions)
    {
      this.fileChannel =
        Objects.requireNonNull(inChannel, "channel");
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
          final var offset = description.dataOffsetWithinSection();
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
            new UncloseableSeekableByteChannel(this.fileChannel);

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
