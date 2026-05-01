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
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImage2DMipMapDeclarations;
import com.io7m.calino.api.CLNSectionWritableImage2DType;
import com.io7m.calino.api.CLWritableMipMaps2DType;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;
import com.io7m.wendover.core.UncloseableSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.nio.channels.WritableByteChannel;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static java.lang.Integer.toUnsignedLong;

/**
 * A writable image 2D section.
 */

final class CLN2SectionWritableImage2D
  extends CLN2SectionWritableAbstract
  implements CLNSectionWritableImage2DType
{
  CLN2SectionWritableImage2D(
    final CloseableCollectionType<CLNException> resources,
    final CLNOnCloseOperationType<CLN2SectionWritableAbstract> inOnClose)
    throws IOException
  {
    super(CLNIdentifiers.sectionImage2DIdentifier(), resources, inOnClose);
  }

  @Override
  public CLWritableMipMaps2DType createMipMaps(
    final CLNImage2DMipMapDeclarations mipMapDeclarations)
    throws IOException
  {
    final var mipMaps =
      mipMapDeclarations.mipMaps();
    final var descriptions =
      new ArrayList<CLNImage2DDescription>(mipMaps.size());

    final var writer = this.writer();

    writer.writeU32BE(toUnsignedLong(mipMaps.size()));

    for (final var mipMap : mipMaps) {
      writer.writeU32BE(toUnsignedLong(mipMap.mipMapLevel()));
      writer.writeU64BE(0L);
      writer.writeU64BE(mipMap.sizeUncompressed());
      writer.writeU64BE(mipMap.sizeCompressed());
      writer.writeU32BE(toUnsignedLong(mipMap.crc32()));
    }

    writer.align(mipMapDeclarations.texelBlockAlignment());

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
      writer.align(mipMapDeclarations.texelBlockAlignment());
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

    return new MipMaps2D(
      this.sectionDataChannel(),
      descriptions
    );
  }

  private static final class MipMaps2D
    implements CLWritableMipMaps2DType
  {
    private final SeekableByteChannel fileChannel;
    private final List<CLNImage2DDescription> descriptions;

    MipMaps2D(
      final SeekableByteChannel inChannel,
      final List<CLNImage2DDescription> inDescriptions)
    {
      this.fileChannel =
        Objects.requireNonNull(inChannel, "channel");
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
          this.fileChannel.position(description.dataOffsetWithinSection());

          final var closeShieldChannel =
            new UncloseableSeekableByteChannel(this.fileChannel);

          return new SubrangeSeekableByteChannel(
            closeShieldChannel,
            description.dataOffsetWithinSection(),
            description.dataSizeCompressed()
          );
        }
      }

      throw new IllegalArgumentException(
        "No such mipmap with level " + mipMapLevel);
    }
  }
}
