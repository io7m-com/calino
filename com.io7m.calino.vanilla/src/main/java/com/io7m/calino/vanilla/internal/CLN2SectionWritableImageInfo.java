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

import com.io7m.calino.api.CLNByteOrder;
import com.io7m.calino.api.CLNChannelsLayoutDescriptionType;
import com.io7m.calino.api.CLNChannelsTypeDescriptionType;
import com.io7m.calino.api.CLNColorSpaceType;
import com.io7m.calino.api.CLNCompressionMethodType;
import com.io7m.calino.api.CLNCoordinateSystem;
import com.io7m.calino.api.CLNDescribableType;
import com.io7m.calino.api.CLNException;
import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.api.CLNImageFlagType;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionWritableImageInfoType;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.seltzer.io.SIOException;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Set;

import static java.lang.Integer.toUnsignedLong;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A writable image info section.
 */

final class CLN2SectionWritableImageInfo
  extends CLN2SectionWritableAbstract
  implements CLNSectionWritableImageInfoType
{
  CLN2SectionWritableImageInfo(
    final CloseableCollectionType<CLNException> resources,
    final CLNOnCloseOperationType<CLN2SectionWritableAbstract> inOnClose)
    throws IOException
  {
    super(CLNIdentifiers.sectionImageInfoIdentifier(), resources, inOnClose);
  }

  @Override
  public void setImageInfo(
    final CLNImageInfo info)
    throws IOException
  {
    final var writer = this.writer();

    writer.writeU32BE(info.sizeX());
    writer.writeU32BE(info.sizeY());
    writer.writeU32BE(info.sizeZ());

    writeChannelsLayout(writer, info.channelsLayout());
    writeChannelsType(writer, info.channelsType());
    writeCompression(writer, info.compressionMethod());
    writeSupercompression(writer, info.superCompressionMethod());
    writeCoordinateSystem(writer, info.coordinateSystem());
    writeColorSpace(writer, info.colorSpace());
    writeFlags(writer, info.flags());
    writeByteOrder(writer, info.dataByteOrder());
  }

  private static void writeChannelsLayout(
    final BSSWriterRandomAccessType writer,
    final CLNChannelsLayoutDescriptionType channelsLayout)
    throws IOException
  {
    writeDescriptor(writer, channelsLayout.descriptor().getBytes(UTF_8));
  }

  private static void writeChannelsType(
    final BSSWriterRandomAccessType writer,
    final CLNChannelsTypeDescriptionType channelsType)
    throws IOException
  {
    writeDescriptor(writer, channelsType.descriptor().getBytes(UTF_8));
  }

  private static void writeCompression(
    final BSSWriterRandomAccessType writer,
    final CLNCompressionMethodType compressionMethod)
    throws IOException
  {
    writeDescriptor(writer, compressionMethod.descriptor().getBytes(UTF_8));
    writer.writeU64BE(compressionMethod.compressionSectionIdentifier());
    writer.writeU32BE(toUnsignedLong(compressionMethod.blockSizeX()));
    writer.writeU32BE(toUnsignedLong(compressionMethod.blockSizeY()));
    writer.writeU32BE(toUnsignedLong(compressionMethod.blockAlignment()));
  }

  private static void writeSupercompression(
    final BSSWriterRandomAccessType writer,
    final CLNSuperCompressionMethodType method)
    throws IOException
  {
    writeDescriptor(writer, method.descriptor().getBytes(UTF_8));
    writer.writeU64BE(method.compressionSectionIdentifier());
  }

  private static void writeCoordinateSystem(
    final BSSWriterRandomAccessType writer,
    final CLNCoordinateSystem system)
    throws IOException
  {
    writeDescriptor(writer, system.descriptor().getBytes(UTF_8));
  }

  private static void writeColorSpace(
    final BSSWriterRandomAccessType writer,
    final CLNColorSpaceType colorSpace)
    throws IOException
  {
    writeDescriptor(writer, colorSpace.descriptor().getBytes(UTF_8));
  }

  private static void writeDescriptor(
    final BSSWriterRandomAccessType writer,
    final byte[] bytes)
    throws SIOException
  {
    writer.writeU32BE(toUnsignedLong(bytes.length));
    writer.writeBytes(bytes);

    final var positionThen = writer.offsetCurrentRelative();
    writer.align(4);
    final var positionNow = writer.offsetCurrentRelative();
    if (positionThen != positionNow) {
      writer.seekTo(positionNow - 1L);
      writer.writeU8(0);
    }
  }

  private static void writeFlags(
    final BSSWriterRandomAccessType writer,
    final Set<CLNImageFlagType> flags)
    throws IOException
  {
    final var flagsSorted = new ArrayList<>(flags);
    flagsSorted.sort(Comparator.comparing(CLNDescribableType::descriptor));
    writer.writeU32BE(toUnsignedLong(flagsSorted.size()));

    for (final var flag : flagsSorted) {
      writeDescriptor(writer, flag.descriptor().getBytes(UTF_8));
    }
  }

  private static void writeByteOrder(
    final BSSWriterRandomAccessType writer,
    final CLNByteOrder dataByteOrder)
    throws IOException
  {
    writeDescriptor(writer, dataByteOrder.descriptor().getBytes(UTF_8));
  }
}
