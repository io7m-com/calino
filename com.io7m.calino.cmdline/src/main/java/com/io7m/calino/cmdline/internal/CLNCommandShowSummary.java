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

import com.beust.jcommander.Parameters;
import com.io7m.calino.api.CLNCompressionMethodStandard;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.api.CLNVersion;
import com.io7m.claypot.core.CLPCommandContextType;

import java.io.IOException;
import java.util.List;
import java.util.Objects;

/**
 * The 'show-summary' command.
 */

@Parameters(commandDescription = "Display information about texture files.")
public final class CLNCommandShowSummary extends CLNAbstractReadFileCommand
{
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
        return summarize2d(fileParsed.version(), info, mipmaps);
      }
    }

    return Status.SUCCESS;
  }

  private static Status summarize2d(
    final CLNVersion version,
    final CLNImageInfo info,
    final List<CLNImage2DDescription> mipmaps)
  {
    final var summary = new StringBuilder(128);
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

    summary.append(" (");
    summary.append(mipmaps.size());
    summary.append(" mipmaps)");

    System.out.println(summary);
    return Status.SUCCESS;
  }

  @Override
  public String name()
  {
    return "show-summary";
  }
}
