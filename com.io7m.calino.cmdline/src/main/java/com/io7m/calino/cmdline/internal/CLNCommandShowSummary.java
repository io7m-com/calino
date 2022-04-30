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
import com.io7m.calino.api.CLNCompressionMethodStandard;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNImageCubeDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.api.CLNVersion;
import com.io7m.claypot.core.CLPCommandContextType;

import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;

/**
 * The 'show-summary' command.
 */

@Parameters(commandDescription = "Display information about texture files.")
public final class CLNCommandShowSummary extends CLNAbstractReadFileCommand
{
  @Parameter(
    required = false,
    description = "Show all mipmaps",
    arity = 1,
    names = "--show-mipmaps")
  private boolean showAllMipMaps;

  /**
   * The 'show-summary' command.
   *
   * @param inContext The context
   */

  public CLNCommandShowSummary(
    final CLPCommandContextType inContext)
  {
    super(inContext);
  }

  private Status summarizeArray(
    final CLNVersion version,
    final CLNImageInfo info,
    final List<CLNImageArrayDescription> mipmaps)
  {
    final var summary = new StringBuilder(128);
    summarizeInfo(version, info, summary);

    final var levels = new HashSet<>();
    for (final var mipmap : mipmaps) {
      levels.add(Integer.valueOf(mipmap.mipMapLevel()));
    }

    summary.append(" (");
    summary.append(levels.size());
    summary.append(" mipmap levels, ");
    summary.append(mipmaps.size());
    summary.append(" images)");

    System.out.println(summary);

    if (this.showAllMipMaps) {
      for (final var mipMap : mipmaps) {
        System.out.printf(
          "mipMapArray (level %s) (layer %s) (offset %s) (size-compressed %s) (size-uncompressed %s) (crc32 0x%s)%n",
          Integer.toUnsignedString(mipMap.mipMapLevel()),
          Integer.toUnsignedString(mipMap.layer()),
          Long.toUnsignedString(mipMap.dataOffsetWithinSection()),
          Long.toUnsignedString(mipMap.dataSizeCompressed()),
          Long.toUnsignedString(mipMap.dataSizeUncompressed()),
          Integer.toUnsignedString(mipMap.crc32Uncompressed(), 16)
        );
      }
    }

    return Status.SUCCESS;
  }

  private static void summarizeInfo(
    final CLNVersion version,
    final CLNImageInfo info,
    final StringBuilder summary)
  {
    summary.append("calino ");
    summary.append(version);
    summary.append(" texture: ");

    summary.append(info.showSize());
    summary.append(' ');
    summary.append(info.channelsLayout().descriptor());
    summary.append(' ');
    summary.append(info.channelsType().descriptor());

    summary.append(' ');
    summary.append(
      switch (info.dataByteOrder()) {
        case BIG_ENDIAN -> "big-endian";
        case LITTLE_ENDIAN -> "little-endian";
      });

    final var compression = info.compressionMethod();
    if (!Objects.equals(
      compression,
      CLNCompressionMethodStandard.UNCOMPRESSED)) {
      summary.append(" (compression ");
      summary.append(compression.descriptor());
      summary.append(")");
    }

    final var superCompression = info.superCompressionMethod();
    if (!Objects.equals(
      superCompression,
      CLNSuperCompressionMethodStandard.UNCOMPRESSED)) {
      summary.append(" (supercompression ");
      summary.append(superCompression.descriptor());
      summary.append(")");
    }
  }

  private Status summarizeCube(
    final CLNVersion version,
    final CLNImageInfo info,
    final List<CLNImageCubeDescription> mipmaps)
  {
    final var summary = new StringBuilder(128);
    summarizeInfo(version, info, summary);

    final var levels = new HashSet<>();
    for (final var mipmap : mipmaps) {
      levels.add(Integer.valueOf(mipmap.mipMapLevel()));
    }

    summary.append(" (");
    summary.append(levels.size());
    summary.append(" mipmap levels, ");
    summary.append(mipmaps.size());
    summary.append(" images)");

    System.out.println(summary);

    if (this.showAllMipMaps) {
      for (final var mipMap : mipmaps) {
        System.out.printf(
          "mipMapCube (level %s) (face %s) (offset %s) (size-compressed %s) (size-uncompressed %s) (crc32 0x%s)%n",
          Integer.toUnsignedString(mipMap.mipMapLevel()),
          mipMap.face(),
          Long.toUnsignedString(mipMap.dataOffsetWithinSection()),
          Long.toUnsignedString(mipMap.dataSizeCompressed()),
          Long.toUnsignedString(mipMap.dataSizeUncompressed()),
          Integer.toUnsignedString(mipMap.crc32Uncompressed(), 16)
        );
      }
    }

    return Status.SUCCESS;
  }

  private Status summarize2d(
    final CLNVersion version,
    final CLNImageInfo info,
    final List<CLNImage2DDescription> mipmaps)
  {
    final var summary = new StringBuilder(128);
    summarizeInfo(version, info, summary);

    summary.append(" (");
    summary.append(mipmaps.size());
    summary.append(" mipmap levels)");

    System.out.println(summary);

    if (this.showAllMipMaps) {
      for (final var mipMap : mipmaps) {
        System.out.printf(
          "mipMap2d (level %s) (offset %s) (size-compressed %s) (size-uncompressed %s) (crc32 0x%s)%n",
          Integer.toUnsignedString(mipMap.mipMapLevel()),
          Long.toUnsignedString(mipMap.dataOffsetWithinSection()),
          Long.toUnsignedString(mipMap.dataSizeCompressed()),
          Long.toUnsignedString(mipMap.dataSizeUncompressed()),
          Integer.toUnsignedString(mipMap.crc32Uncompressed(), 16)
        );
      }
    }

    return Status.SUCCESS;
  }

  @Override
  public String extendedHelp()
  {
    return this.calinoStrings().format("cmd.show-summary.helpExt");
  }

  @Override
  protected Status executeWithReadFile(
    final CLNFileReadableType fileParsed)
    throws IOException
  {
    final var sectionInfoOpt =
      fileParsed.openImageInfo();

    if (sectionInfoOpt.isPresent()) {
      final var sectionInfo =
        sectionInfoOpt.get();
      final var info =
        sectionInfo.info();
      final var section2dOpt =
        fileParsed.openImage2D();

      if (section2dOpt.isPresent()) {
        final var section2d = section2dOpt.get();
        final var mipmaps = section2d.mipMapDescriptions();
        return this.summarize2d(fileParsed.version(), info, mipmaps);
      }

      final var sectionCubeOpt =
        fileParsed.openImageCube();

      if (sectionCubeOpt.isPresent()) {
        final var sectionCube = sectionCubeOpt.get();
        final var mipmaps = sectionCube.mipMapDescriptions();
        return this.summarizeCube(fileParsed.version(), info, mipmaps);
      }

      final var sectionArrayOpt =
        fileParsed.openImageArray();

      if (sectionArrayOpt.isPresent()) {
        final var sectionArray = sectionArrayOpt.get();
        final var mipmaps = sectionArray.mipMapDescriptions();
        return this.summarizeArray(fileParsed.version(), info, mipmaps);
      }
    }

    return Status.SUCCESS;
  }

  @Override
  public String name()
  {
    return "show-summary";
  }
}
