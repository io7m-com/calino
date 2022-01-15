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
import com.io7m.calino.api.CLNDescribableType;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.claypot.core.CLPCommandContextType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.stream.Collectors;

import static com.io7m.claypot.core.CLPCommandType.Status.FAILURE;
import static com.io7m.claypot.core.CLPCommandType.Status.SUCCESS;

/**
 * The 'show-image-info' command.
 */

@Parameters(commandDescription = "Display texture file image info.")
public final class CLNCommandShowImageInfo extends CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandShowImageInfo.class);

  /**
   * The 'show-image-info' command.
   *
   * @param inContext The context
   */

  public CLNCommandShowImageInfo(
    final CLPCommandContextType inContext)
  {
    super(inContext);
  }

  @Override
  public String extendedHelp()
  {
    return this.calinoStrings().format("cmd.show-image-info.helpExt");
  }

  @Override
  protected Status executeWithReadFile(
    final CLNFileReadableType fileParsed)
    throws IOException
  {
    final var sectionImageInfo =
      fileParsed.openImageInfo();

    if (sectionImageInfo.isEmpty()) {
      LOG.error("no image info section is present");
      return FAILURE;
    }

    final var imageInfo =
      sectionImageInfo.get()
        .info();

    System.out.printf(
      "%-24s: %s%n",
      "Size",
      imageInfo.showSize());
    System.out.printf(
      "%-24s: %s%n",
      "Channel Layout",
      imageInfo.channelsLayout().descriptor());
    System.out.printf(
      "%-24s: %s%n",
      "Channel Type",
      imageInfo.channelsType().descriptor());
    System.out.printf(
      "%-24s: %s%n",
      "Color Space",
      imageInfo.colorSpace().descriptor());
    System.out.printf(
      "%-24s: %s%n",
      "Flags",
      imageInfo.flags()
        .stream()
        .map(CLNDescribableType::descriptor)
        .collect(Collectors.joining(","))
    );
    System.out.printf(
      "%-24s: %s%n",
      "Coordinate System",
      imageInfo.coordinateSystem().descriptor());
    System.out.printf(
      "%-24s: %s%n",
      "Compression",
      imageInfo.compressionMethod().descriptor());
    System.out.printf(
      "%-24s: %s%n",
      "Super Compression",
      imageInfo.superCompressionMethod().descriptor());
    System.out.printf(
      "%-24s: %s octets%n",
      "Texel Block Alignment",
      imageInfo.texelBlockAlignment());

    return SUCCESS;
  }

  @Override
  public String name()
  {
    return "show-image-info";
  }
}
