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
import com.io7m.calino.api.CLNImageFlagType;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionWritableImageInfoType;
import com.io7m.calino.api.CLNSectionWritableType;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Objects;
import java.util.Set;

import static java.lang.Integer.toUnsignedLong;
import static java.nio.charset.StandardCharsets.UTF_8;

public final class CLN1SectionWritableImageInfo
  extends CLN1SectionWritableAbstract
  implements CLNSectionWritableImageInfoType
{
  private final BSSWriterProviderType writers;

  public CLN1SectionWritableImageInfo(
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
  public void setImageInfo(
    final CLNImageInfo info)
    throws IOException
  {
    Objects.requireNonNull(info, "info");

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "imageInfo")) {

        writer.writeU32BE(info.sizeX());
        writer.writeU32BE(info.sizeY());
        writer.writeU32BE(info.sizeZ());

        this.writeChannelsLayout(writer, info.channelsLayout());
        this.writeChannelsType(writer, info.channelsType());
        this.writeCompression(writer, info.compressionMethod());
        this.writeSupercompression(writer, info.superCompressionMethod());
        writeCoordinateSystem(writer, info.coordinateSystem());
        writeColorSpace(writer, info.colorSpace());
        writeFlags(writer, info.flags());
        writeByteOrder(writer, info.dataByteOrder());

        writer.align(16);
      }
    }
  }

  private static void writeByteOrder(
    final BSSWriterRandomAccessType writer,
    final CLNByteOrder dataByteOrder)
    throws IOException
  {
    switch (dataByteOrder) {
      case BIG_ENDIAN -> {
        writer.writeU32BE("byteOrder", 0L);
      }
      case LITTLE_ENDIAN -> {
        writer.writeU32BE("byteOrder", 1L);
      }
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
      final var bytes = flag.descriptor().getBytes(UTF_8);
      writer.writeU32BE(toUnsignedLong(bytes.length));
      writer.writeBytes(bytes);
      writer.align(4);
    }
  }

  private static void writeColorSpace(
    final BSSWriterRandomAccessType writer,
    final CLNColorSpaceType colorSpace)
    throws IOException
  {
    final var bytes = colorSpace.descriptor().getBytes(UTF_8);
    writer.writeU32BE(toUnsignedLong(bytes.length));
    writer.writeBytes(bytes);
    writer.align(4);
  }

  private static void writeCoordinateSystem(
    final BSSWriterRandomAccessType writer,
    final CLNCoordinateSystem system)
    throws IOException
  {
    final var bytes = system.descriptor().getBytes(UTF_8);
    writer.writeU32BE(toUnsignedLong(bytes.length));
    writer.writeBytes(bytes);
    writer.align(4);
  }

  private void writeSupercompression(
    final BSSWriterRandomAccessType writer,
    final CLNSuperCompressionMethodType method)
    throws IOException
  {
    final var bytes = method.descriptor().getBytes(UTF_8);
    writer.writeU32BE(toUnsignedLong(bytes.length));
    writer.writeBytes(bytes);
    writer.align(4);
    writer.writeU64BE(method.compressionSectionIdentifier());
  }

  private void writeCompression(
    final BSSWriterRandomAccessType writer,
    final CLNCompressionMethodType compressionMethod)
    throws IOException
  {
    final var bytes = compressionMethod.descriptor().getBytes(UTF_8);
    writer.writeU32BE(toUnsignedLong(bytes.length));
    writer.writeBytes(bytes);
    writer.align(4);
    writer.writeU64BE(compressionMethod.compressionSectionIdentifier());
    writer.writeU32BE(toUnsignedLong(compressionMethod.blockSizeX()));
    writer.writeU32BE(toUnsignedLong(compressionMethod.blockSizeY()));
    writer.writeU32BE(toUnsignedLong(compressionMethod.blockAlignment()));
  }

  private void writeChannelsType(
    final BSSWriterRandomAccessType writer,
    final CLNChannelsTypeDescriptionType channelsType)
    throws IOException
  {
    final var bytes = channelsType.descriptor().getBytes(UTF_8);
    writer.writeU32BE(toUnsignedLong(bytes.length));
    writer.writeBytes(bytes);
    writer.align(4);
  }

  private void writeChannelsLayout(
    final BSSWriterRandomAccessType writer,
    final CLNChannelsLayoutDescriptionType channelsLayout)
    throws IOException
  {
    final var bytes = channelsLayout.descriptor().getBytes(UTF_8);
    writer.writeU32BE(toUnsignedLong(bytes.length));
    writer.writeBytes(bytes);
    writer.align(4);
  }
}
