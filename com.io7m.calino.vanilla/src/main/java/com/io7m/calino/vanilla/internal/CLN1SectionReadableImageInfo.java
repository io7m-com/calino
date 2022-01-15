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
import com.io7m.calino.api.CLNChannelsTypeDescriptionCustom;
import com.io7m.calino.api.CLNChannelsTypeDescriptionStandard;
import com.io7m.calino.api.CLNChannelsTypeDescriptionType;
import com.io7m.calino.api.CLNColorSpaceCustom;
import com.io7m.calino.api.CLNColorSpaceStandard;
import com.io7m.calino.api.CLNColorSpaceType;
import com.io7m.calino.api.CLNCompressionMethodCustom;
import com.io7m.calino.api.CLNCompressionMethodStandard;
import com.io7m.calino.api.CLNCompressionMethodType;
import com.io7m.calino.api.CLNCoordinateSystem;
import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNImageFlagCustom;
import com.io7m.calino.api.CLNImageFlagStandard;
import com.io7m.calino.api.CLNImageFlagType;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;

import java.io.IOException;
import java.text.ParseException;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

import static java.lang.Long.toUnsignedString;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A readable image info section.
 */

public final class CLN1SectionReadableImageInfo
  extends CLN1SectionReadableAbstract implements CLNSectionReadableImageInfoType
{
  /**
   * A readable image info section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  CLN1SectionReadableImageInfo(
    final BSSReaderRandomAccessType inReader,
    final CLNParseRequest inRequest,
    final CLNFileSectionDescription inDescription)
  {
    super(inReader, inRequest, inDescription);
  }

  private static CLNCompressionMethodType parseCompressionMethod(
    final String text,
    final long sectionIdentifier,
    final long blockSizeX,
    final long blockSizeY,
    final long blockAlignment)
  {
    final var knownMethods =
      CLNCompressionMethodStandard.values();

    for (final var known : knownMethods) {
      if (Objects.equals(text, known.descriptor())) {
        return known;
      }
    }

    return new CLNCompressionMethodCustom(
      text,
      sectionIdentifier,
      (int) blockSizeX,
      (int) blockSizeY,
      (int) blockAlignment
    );
  }

  private static CLNChannelsTypeDescriptionType parseTypeDescriptor(
    final String text)
  {
    for (final var knownType : CLNChannelsTypeDescriptionStandard.values()) {
      if (Objects.equals(knownType.descriptor(), text)) {
        return knownType;
      }
    }
    return new CLNChannelsTypeDescriptionCustom(text);
  }

  private static String makeString(
    final byte[] bytes)
  {
    // CHECKSTYLE:OFF
    return new String(bytes, UTF_8);
    // CHECKSTYLE:ON
  }

  private static CLNByteOrder readByteOrder(
    final BSSReaderRandomAccessType reader)
    throws IOException
  {
    final var byteOrder = reader.readU32BE("byteOrder");
    if (byteOrder == 0L) {
      return CLNByteOrder.BIG_ENDIAN;
    }
    if (byteOrder == 1L) {
      return CLNByteOrder.LITTLE_ENDIAN;
    }

    final var lineSeparator = System.lineSeparator();
    final var error = new StringBuilder(64);
    error.append("Unparseable byte order.");
    error.append(lineSeparator);
    error.append("  Offset: 0x");
    error.append(toUnsignedString(reader.offsetCurrentAbsolute(), 16));
    error.append(lineSeparator);
    error.append("  Problem: Expected a value in the range [0, 1]");
    error.append(lineSeparator);
    error.append("  Received: 0x");
    error.append(toUnsignedString(byteOrder, 16));
    error.append(lineSeparator);
    throw new IOException(error.toString());
  }

  private static CLNImageFlagType readFlag(
    final String text)
  {
    for (final var standard : CLNImageFlagStandard.values()) {
      if (Objects.equals(standard.descriptor(), text)) {
        return standard;
      }
    }
    return new CLNImageFlagCustom(text);
  }

  @Override
  public CLNImageInfo info()
    throws IOException
  {
    final var reader =
      this.reader();
    final var fileOffset =
      this.fileSectionDescription().fileOffset();
    final var sectionSize =
      this.description().size();

    reader.seekTo(fileOffset);
    reader.skip(16L);

    try (var subReader =
           reader.createSubReaderAtBounded(
             "imageInfo", 0L, sectionSize)) {

      final var sizeX =
        subReader.readU32BE("sizeX");
      final var sizeY =
        subReader.readU32BE("sizeY");
      final var sizeZ =
        subReader.readU32BE("sizeZ");

      final var layout =
        this.readChannelsLayout(subReader);
      final var type =
        this.readChannelsType(subReader);
      final var compression =
        this.readCompression(subReader);
      final var superCompression =
        this.readSuperCompression(subReader);
      final var coordinateSystem =
        this.readCoordinateSystem(subReader);
      final var colorSpace =
        this.readColorSpace(subReader);
      final var flags =
        this.readImageFlags(subReader);
      final var byteOrder =
        readByteOrder(subReader);

      return new CLNImageInfo(
        (int) (sizeX & 0xffff_ffffL),
        (int) (sizeY & 0xffff_ffffL),
        (int) (sizeZ & 0xffff_ffffL),
        layout,
        type,
        compression,
        superCompression,
        coordinateSystem,
        colorSpace,
        flags,
        byteOrder
      );
    }
  }

  private Set<CLNImageFlagType> readImageFlags(
    final BSSReaderRandomAccessType parent)
    throws IOException
  {
    var consumed = 0L;
    final var flags = new HashSet<CLNImageFlagType>();
    try (var reader =
           parent.createSubReaderAt("flags", 0L)) {

      final var flagCount =
        reader.readU32BE("flagCount");

      for (long index = 0L;
           Long.compareUnsigned(index, flagCount) < 0;
           ++index) {

        final var length =
          reader.readU32BE("descriptorLength");

        this.checkDescriptorLengthLimit(
          length, this.request().descriptorLengthLimit());

        final var bytes = new byte[(int) length];
        reader.readBytes(bytes);
        reader.align(4);
        flags.add(readFlag(makeString(bytes)));
      }

      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);
      return flags;
    }
  }

  private CLNColorSpaceType readColorSpace(
    final BSSReaderRandomAccessType parent)
    throws IOException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("colorSpace", 0L)) {

      final var length =
        reader.readU32BE("descriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);
      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);
      final var text = makeString(bytes);

      for (final var standard : CLNColorSpaceStandard.values()) {
        if (Objects.equals(standard.descriptor(), text)) {
          return standard;
        }
      }
      return new CLNColorSpaceCustom(text);
    }
  }

  private CLNCoordinateSystem readCoordinateSystem(
    final BSSReaderRandomAccessType parent)
    throws IOException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("coordinateSystem", 0L)) {

      final var length =
        reader.readU32BE("descriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);
      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);

      try {
        return CLNCoordinateSystem.parseDescriptor(makeString(bytes));
      } catch (final ParseException e) {
        final var lineSeparator = System.lineSeparator();
        final var error = new StringBuilder(64);
        error.append("Unparseable coordinate descriptor.");
        error.append(lineSeparator);
        error.append("  Offset: 0x");
        error.append(toUnsignedString(parent.offsetCurrentAbsolute(), 16));
        error.append(lineSeparator);
        error.append("  Problem: ");
        error.append(e.getMessage());
        error.append(lineSeparator);
        throw new IOException(error.toString(), e);
      }
    }
  }

  private CLNSuperCompressionMethodType readSuperCompression(
    final BSSReaderRandomAccessType parent)
    throws IOException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("superCompression", 0L)) {

      final var length =
        reader.readU32BE("descriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);

      final var sectionIdentifier =
        reader.readU64BE("compressionSectionIdentifier");

      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);
      return CLNSuperCompressionMethodType.parse(
        makeString(bytes),
        sectionIdentifier
      );
    }
  }

  private void checkDescriptorLengthLimit(
    final long length,
    final long limit)
    throws IOException
  {
    if (Long.compareUnsigned(length, limit) > 0) {
      throw new IOException(
        this.errorLimitExceeded(length, limit, "descriptor length limit")
      );
    }
  }

  private CLNCompressionMethodType readCompression(
    final BSSReaderRandomAccessType parent)
    throws IOException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("compression", 0L)) {

      final var length =
        reader.readU32BE("descriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);

      final var sectionIdentifier =
        reader.readU64BE("compressionSectionIdentifier");
      final var blockSizeX =
        reader.readU32BE("blockSizeX");
      final var blockSizeY =
        reader.readU32BE("blockSizeY");
      final var blockAlignment =
        reader.readU32BE("blockAlignment");

      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);
      return parseCompressionMethod(
        makeString(bytes),
        sectionIdentifier,
        blockSizeX,
        blockSizeY,
        blockAlignment
      );
    }
  }

  private CLNChannelsTypeDescriptionType readChannelsType(
    final BSSReaderRandomAccessType parent)
    throws IOException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("channelsType", 0L)) {

      final var length =
        reader.readU32BE("descriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);
      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);
      return parseTypeDescriptor(makeString(bytes));
    }
  }

  private CLNChannelsLayoutDescriptionType readChannelsLayout(
    final BSSReaderRandomAccessType parent)
    throws IOException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("channelsLayout", 0L)) {

      final var length =
        reader.readU32BE("descriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);
      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);

      try {
        return CLNChannelsLayoutDescriptionType.parseLayoutDescriptor(makeString(
          bytes));
      } catch (final ParseException e) {
        final var lineSeparator = System.lineSeparator();
        final var error = new StringBuilder(64);
        error.append("Unparseable layout descriptor.");
        error.append(lineSeparator);
        error.append("  Offset: 0x");
        error.append(toUnsignedString(parent.offsetCurrentAbsolute(), 16));
        error.append(lineSeparator);
        error.append("  Problem: ");
        error.append(e.getMessage());
        error.append(lineSeparator);
        throw new IOException(error.toString(), e);
      }
    }
  }
}
