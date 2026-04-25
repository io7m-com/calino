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

import com.io7m.calino.api.CLNDescribableType;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.quarrel.core.QStringType.QLocalize;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * The 'show-image-info' command.
 */

public final class CLNCommandShowImageInfo extends CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandShowImageInfo.class);

  /**
   * The 'show-image-info' command.
   */

  public CLNCommandShowImageInfo()
  {
    super(
      new QCommandMetadata(
        "show-image-info",
        new QConstant("Display texture file image info."),
        Optional.of(new QLocalize("cmd.show-image-info.helpExt"))
      )
    );
  }

  @Override
  protected List<QParameterNamedType<?>>
  onListNamedParametersWithFile()
  {
    return List.of();
  }

  @Override
  protected QCommandStatus executeWithReadFile(
    final QCommandContextType context,
    final CLNFileReadableType fileParsed)
    throws IOException
  {
    final var sectionImageInfo =
      fileParsed.openImageInfo();

    if (sectionImageInfo.isEmpty()) {
      LOG.error("No image info section is present");
      return QCommandStatus.FAILURE;
    }

    final var imageInfo =
      sectionImageInfo.get()
        .info();

    final var output =
      context.output();

    output.printf(
      "%-24s: %s%n",
      "Size",
      imageInfo.showSize());
    output.printf(
      "%-24s: %s%n",
      "Channel Layout",
      imageInfo.channelsLayout().descriptor());
    output.printf(
      "%-24s: %s%n",
      "Channel Type",
      imageInfo.channelsType().descriptor());
    output.printf(
      "%-24s: %s%n",
      "Color Space",
      imageInfo.colorSpace().descriptor());
    output.printf(
      "%-24s: %s%n",
      "Flags",
      imageInfo.flags()
        .stream()
        .map(CLNDescribableType::descriptor)
        .collect(Collectors.joining(","))
    );
    output.printf(
      "%-24s: %s%n",
      "Coordinate System",
      imageInfo.coordinateSystem().descriptor());
    output.printf(
      "%-24s: %s%n",
      "Compression",
      imageInfo.compressionMethod().descriptor());
    output.printf(
      "%-24s: %s%n",
      "Super Compression",
      imageInfo.superCompressionMethod().descriptor());
    output.printf(
      "%-24s: %s octets%n",
      "Texel Block Alignment",
      imageInfo.texelBlockAlignment());

    return QCommandStatus.SUCCESS;
  }
}
