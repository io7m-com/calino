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
import com.io7m.calino.api.CLNImageCubeDescription;
import com.io7m.calino.api.CLNImageCubeMipMapDeclaration;
import com.io7m.calino.api.CLNImageCubeMipMapDeclarations;
import com.io7m.calino.api.CLNSectionWritableImageCubeType;
import com.io7m.calino.api.CLNSectionWritableType;
import com.io7m.calino.api.CLWritableMipMapsCubeType;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.wendover.core.CloseShieldSeekableByteChannel;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.nio.channels.WritableByteChannel;
import java.util.EnumMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.TreeMap;

import static java.lang.Integer.toUnsignedLong;

/**
 * A writable cube image section.
 */

public final class CLN1SectionWritableImageCube
  extends CLN1SectionWritableAbstract
  implements CLNSectionWritableImageCubeType
{
  private final BSSWriterProviderType writers;

  /**
   * A writable cube image section.
   *
   * @param inWriters    A writer provider
   * @param inOnClose    A function executed on closing
   * @param inRequest    A write request
   * @param inIdentifier An identifier
   * @param inWriter     A writer
   */

  public CLN1SectionWritableImageCube(
    final BSSWriterProviderType inWriters,
    final BSSWriterRandomAccessType inWriter,
    final CLNWriteRequest inRequest,
    final long inIdentifier,
    final CLNOnCloseOperationType<CLNSectionWritableType> inOnClose)
  {
    super(inWriter, inRequest, inIdentifier, inOnClose);
    this.writers = Objects.requireNonNull(inWriters, "inWriters");
  }

  private static int maxUnsigned(
    final int x,
    final int y)
  {
    if (Integer.compareUnsigned(x, y) > 0) {
      return x;
    }
    return y;
  }

  @Override
  public CLWritableMipMapsCubeType createMipMaps(
    final CLNImageCubeMipMapDeclarations mipMapCreate)
    throws IOException
  {
    Objects.requireNonNull(mipMapCreate, "mipMaps");

    final var mipMaps =
      mipMapCreate.mipMaps();
    final var descriptionsByLevel =
      new TreeMap<Integer, EnumMap<CLNCubeFace, CLNImageCubeDescription>>();

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "imageCube")) {

        writer.writeU32BE(toUnsignedLong(mipMaps.size()));

        final var facesOrdered = CLNCubeFace.facesInOrder();

        /*
         * Reserve space for all the mipmap descriptions.
         */

        reserveSpaceForMipMapDescriptions(mipMaps, writer, facesOrdered);

        /*
         * Reserve space for all the mipmap image data.
         */

        writer.align(mipMapCreate.texelBlockAlignment());

        reserveSpaceForMipMapImageData(
          mipMapCreate,
          mipMaps,
          descriptionsByLevel,
          writer,
          facesOrdered);

        writer.writeU8(0);
        writer.seekTo(4L);

        /*
         * Now serialize all the mipmap descriptions, now that all the offsets
         * have been recorded.
         */

        serializeAllDescriptions(descriptionsByLevel, writer);
      }
    }

    return new MipMapsCube(
      this.request().channel(),
      this.offsetStartData(),
      descriptionsByLevel
    );
  }

  private static void reserveSpaceForMipMapDescriptions(
    final List<CLNImageCubeMipMapDeclaration> mipMaps,
    final BSSWriterRandomAccessType writer,
    final List<CLNCubeFace> facesOrdered)
    throws IOException
  {
    for (final var mipMap : mipMaps) {
      writer.writeU32BE(toUnsignedLong(mipMap.mipMapLevel()));

      for (final var faceName : facesOrdered) {
        writer.writeU8(0);
        writer.seekTo(writer.offsetCurrentRelative() - 1L);

        final var face =
          switch (faceName) {
            case X_POSITIVE -> mipMap.xPositive();
            case X_NEGATIVE -> mipMap.xNegative();
            case Y_POSITIVE -> mipMap.yPositive();
            case Y_NEGATIVE -> mipMap.yNegative();
            case Z_POSITIVE -> mipMap.zPositive();
            case Z_NEGATIVE -> mipMap.zNegative();
          };

        writer.writeU64BE(0L);
        writer.writeU64BE(face.sizeUncompressed());
        writer.writeU64BE(face.sizeCompressed());
        writer.writeU32BE(toUnsignedLong(face.crc32()));
      }
    }
  }

  private static void reserveSpaceForMipMapImageData(
    final CLNImageCubeMipMapDeclarations mipMapCreate,
    final List<CLNImageCubeMipMapDeclaration> mipMaps,
    final TreeMap<Integer, EnumMap<CLNCubeFace, CLNImageCubeDescription>> descriptionsByLevel,
    final BSSWriterRandomAccessType writer,
    final List<CLNCubeFace> facesOrdered)
    throws IOException
  {
    for (final var mipMap : mipMaps) {
      for (final var faceName : facesOrdered) {
        writer.writeU8(0);
        writer.seekTo(writer.offsetCurrentRelative() - 1L);

        final var face =
          switch (faceName) {
            case X_POSITIVE -> mipMap.xPositive();
            case X_NEGATIVE -> mipMap.xNegative();
            case Y_POSITIVE -> mipMap.yPositive();
            case Y_NEGATIVE -> mipMap.yNegative();
            case Z_POSITIVE -> mipMap.zPositive();
            case Z_NEGATIVE -> mipMap.zNegative();
          };

        final var description =
          new CLNImageCubeDescription(
            mipMap.mipMapLevel(),
            faceName,
            writer.offsetCurrentRelative(),
            face.sizeUncompressed(),
            face.sizeCompressed(),
            face.crc32()
          );

        saveDescription(descriptionsByLevel, mipMap, faceName, description);
        writer.skip(face.sizeCompressed());
        writer.align(mipMapCreate.texelBlockAlignment());
      }
    }
  }

  private static void serializeAllDescriptions(
    final TreeMap<Integer, EnumMap<CLNCubeFace, CLNImageCubeDescription>> descriptionsByLevel,
    final BSSWriterRandomAccessType writer)
    throws IOException
  {
    final var levels =
      descriptionsByLevel.descendingKeySet();

    for (final int level : levels) {
      final var byFace =
        descriptionsByLevel.get(Integer.valueOf(level));

      writer.writeU32BE(toUnsignedLong(level));
      for (final var face : CLNCubeFace.facesInOrder()) {
        final var description = byFace.get(face);
        writer.writeU64BE(description.dataOffsetWithinSection());
        writer.writeU64BE(description.dataSizeUncompressed());
        writer.writeU64BE(description.dataSizeCompressed());
        writer.writeU32BE(toUnsignedLong(description.crc32Uncompressed()));
      }
    }
  }

  private static void saveDescription(
    final Map<Integer, EnumMap<CLNCubeFace, CLNImageCubeDescription>> descriptionsByLevel,
    final CLNImageCubeMipMapDeclaration mipMap,
    final CLNCubeFace faceName,
    final CLNImageCubeDescription description)
  {
    var byFace =
      descriptionsByLevel.get(Integer.valueOf(mipMap.mipMapLevel()));
    if (byFace == null) {
      byFace = new EnumMap<>(CLNCubeFace.class);
    }
    byFace.put(faceName, description);
    descriptionsByLevel.put(Integer.valueOf(mipMap.mipMapLevel()), byFace);
  }

  private static final class MipMapsCube implements CLWritableMipMapsCubeType
  {
    private final SeekableByteChannel fileChannel;
    private final long fileSectionDataStart;
    private final Map<Integer, EnumMap<CLNCubeFace, CLNImageCubeDescription>> descriptions;

    MipMapsCube(
      final SeekableByteChannel inChannel,
      final long inFileSectionDataStart,
      final Map<Integer, EnumMap<CLNCubeFace, CLNImageCubeDescription>> inDescriptions)
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
      final CLNCubeFace face)
      throws IOException
    {
      Objects.requireNonNull(face, "face");

      final var byFace =
        this.descriptions.get(Integer.valueOf(mipMapLevel));

      if (byFace != null) {
        final var description = byFace.get(face);
        if (description != null) {
          final var offset =
            this.fileSectionDataStart + description.dataOffsetWithinSection();

          this.fileChannel.position(offset);

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
        new StringBuilder(64)
          .append("No such mipmap with level ")
          .append(mipMapLevel)
          .append(" and face ")
          .append(face)
          .toString()
      );
    }
  }
}
