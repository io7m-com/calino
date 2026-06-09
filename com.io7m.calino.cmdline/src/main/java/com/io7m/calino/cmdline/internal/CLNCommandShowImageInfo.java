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

import com.io7m.calino.api.CLNCoordinateSystem;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.quarrel.core.QStringType.QLocalize;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import java.util.List;
import java.util.Optional;

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
    throws Exception
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

    final var mapper =
      JsonMapper.shared();
    final var object =
      mapper.createObjectNode();

    showImageInfo(mapper, object, imageInfo);

    final var writer = mapper.writerWithDefaultPrettyPrinter();
    final var output = context.output();
    output.write(writer.writeValueAsString(object));
    output.println();
    output.flush();
    return QCommandStatus.SUCCESS;
  }

  static void showImageInfo(
    final JsonMapper mapper,
    final ObjectNode object,
    final CLNImageInfo imageInfo)
  {
    object.put("SizeX", imageInfo.sizeX());
    object.put("SizeY", imageInfo.sizeY());
    object.put("SizeZ", imageInfo.sizeZ());
    object.put("Size", imageInfo.showSize());
    object.put("ChannelLayout", imageInfo.channelsLayout().descriptor());
    object.put("ChannelType", imageInfo.channelsType().descriptor());
    object.put("ColorSpace", imageInfo.colorSpace().descriptor());
    object.put("ByteOrder", imageInfo.dataByteOrder().descriptor());

    {
      final var flags = mapper.createArrayNode();
      for (final var flag : imageInfo.flags()) {
        flags.add(flag.descriptor());
      }
      object.set("Flags", flags);
    }

    final CLNCoordinateSystem coordinateSystem = imageInfo.coordinateSystem();
    object.put("CoordinateSystemR", coordinateSystem.axisR().descriptor());
    object.put("CoordinateSystemS", coordinateSystem.axisS().descriptor());
    object.put("CoordinateSystemT", coordinateSystem.axisT().descriptor());
    object.put("CoordinateSystem", coordinateSystem.descriptor());

    object.put("Compression", imageInfo.compressionMethod().descriptor());
    object.put(
      "SuperCompression",
      imageInfo.superCompressionMethod().descriptor());
    object.put("TexelBlockAlignment", imageInfo.texelBlockAlignment());
  }
}
