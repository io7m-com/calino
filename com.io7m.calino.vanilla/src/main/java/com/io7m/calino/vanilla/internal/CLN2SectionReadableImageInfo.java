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
import com.io7m.calino.api.CLNChannelsLayoutDescriptions;
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
import com.io7m.calino.api.CLNException;
import com.io7m.calino.api.CLNImageFlagCustom;
import com.io7m.calino.api.CLNImageFlagStandard;
import com.io7m.calino.api.CLNImageFlagType;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.entomos.core.EoFileSection;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;

import java.io.IOException;
import java.text.ParseException;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import static java.lang.Long.toUnsignedString;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A readable image info section.
 */

public final class CLN2SectionReadableImageInfo
  extends CLN2SectionReadableAbstract
  implements CLNSectionReadableImageInfoType
{
  /**
   * A readable image info section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  CLN2SectionReadableImageInfo(
    final BSSReaderRandomAccessType inReader,
    final CLNParseRequest inRequest,
    final EoFileSection inDescription)
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

  private static String offsetString(
    final BSSReaderRandomAccessType parent)
  {
    return "0x" + toUnsignedString(parent.offsetCurrentAbsolute(), 16);
  }

  private CLNByteOrder readByteOrder(
    final BSSReaderRandomAccessType parent)
    throws CLNException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("ByteOrder", 0L)) {

      final var length =
        reader.readU32BE("DescriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);
      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);
      final var text = makeString(bytes);

      return switch (text) {
        case "BIG_ENDIAN" -> CLNByteOrder.BIG_ENDIAN;
        case "LITTLE_ENDIAN" -> CLNByteOrder.LITTLE_ENDIAN;

        default -> {
          throw new CLNException(
            "Unparseable byte order.",
            Map.ofEntries(
              Map.entry("Offset", offsetString(reader)),
              Map.entry("Expected", "BIG_ENDIAN | LITTLE_ENDIAN"),
              Map.entry("Received", text)
            ),
            "error-byte-order-unparseable",
            Optional.empty()
          );
        }
      };
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  @Override
  public CLNImageInfo info()
    throws CLNException
  {
    try (var subReader = this.sectionDataReader()) {
      final var sizeX =
        subReader.readU32BE("SizeX");
      final var sizeY =
        subReader.readU32BE("SizeY");
      final var sizeZ =
        subReader.readU32BE("SizeZ");

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
        this.readByteOrder(subReader);

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
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  private Set<CLNImageFlagType> readImageFlags(
    final BSSReaderRandomAccessType parent)
    throws CLNException
  {
    var consumed = 0L;
    final var flags = new HashSet<CLNImageFlagType>();
    try (var reader = parent.createSubReaderAt("Flags", 0L)) {
      final var flagCount =
        reader.readU32BE("FlagCount");

      for (long index = 0L;
           Long.compareUnsigned(index, flagCount) < 0;
           ++index) {

        final var length =
          reader.readU32BE("DescriptorLength");

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
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  private CLNColorSpaceType readColorSpace(
    final BSSReaderRandomAccessType parent)
    throws CLNException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("ColorSpace", 0L)) {

      final var length =
        reader.readU32BE("DescriptorLength");

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
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  private CLNCoordinateSystem readCoordinateSystem(
    final BSSReaderRandomAccessType parent)
    throws CLNException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("CoordinateSystem", 0L)) {

      final var length =
        reader.readU32BE("DescriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);
      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);

      final String text = makeString(bytes);
      try {
        return CLNCoordinateSystem.parseDescriptor(text);
      } catch (final ParseException e) {
        throw new CLNException(
          "Unparseable coordinate descriptor.",
          Map.ofEntries(
            Map.entry("Offset", offsetString(reader)),
            Map.entry("Received", text),
            Map.entry("Problem", e.getMessage())
          ),
          "error-coordinate-descriptor-unparseable",
          Optional.empty()
        );
      }
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  private CLNSuperCompressionMethodType readSuperCompression(
    final BSSReaderRandomAccessType parent)
    throws CLNException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("SuperCompression", 0L)) {

      final var length =
        reader.readU32BE("DescriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);

      final var sectionIdentifier =
        reader.readU64BE("CompressionSectionIdentifier");

      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);
      return CLNSuperCompressionMethodType.parse(
        makeString(bytes),
        sectionIdentifier
      );
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  private void checkDescriptorLengthLimit(
    final long length,
    final long limit)
    throws CLNException
  {
    if (Long.compareUnsigned(length, limit) > 0) {
      throw this.errorLimitExceeded(length, limit, "descriptor length limit");
    }
  }

  private CLNCompressionMethodType readCompression(
    final BSSReaderRandomAccessType parent)
    throws CLNException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("Compression", 0L)) {

      final var length =
        reader.readU32BE("DescriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);

      final var sectionIdentifier =
        reader.readU64BE("CompressionSectionIdentifier");
      final var blockSizeX =
        reader.readU32BE("BlockSizeX");
      final var blockSizeY =
        reader.readU32BE("BlockSizeY");
      final var blockAlignment =
        reader.readU32BE("BlockAlignment");

      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);
      return parseCompressionMethod(
        makeString(bytes),
        sectionIdentifier,
        blockSizeX,
        blockSizeY,
        blockAlignment
      );
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  private CLNChannelsTypeDescriptionType readChannelsType(
    final BSSReaderRandomAccessType parent)
    throws CLNException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("ChannelsType", 0L)) {

      final var length =
        reader.readU32BE("DescriptorLength");
      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);
      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);
      return parseTypeDescriptor(makeString(bytes));
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  private CLNChannelsLayoutDescriptionType readChannelsLayout(
    final BSSReaderRandomAccessType parent)
    throws IOException, CLNException
  {
    var consumed = 0L;

    try (var reader =
           parent.createSubReaderAt("ChannelsLayout", 0L)) {

      final var length =
        reader.readU32BE("DescriptorLength");

      this.checkDescriptorLengthLimit(
        length, this.request().descriptorLengthLimit());

      final var bytes = new byte[(int) length];
      reader.readBytes(bytes);
      reader.align(4);
      consumed = reader.offsetCurrentRelative();
      parent.skip(consumed);

      final String text =
        makeString(bytes);

      try {
        return CLNChannelsLayoutDescriptions.parseLayoutDescriptor(text);
      } catch (final ParseException e) {
        throw new CLNException(
          "Unparseable layout descriptor.",
          Map.ofEntries(
            Map.entry("Offset", offsetString(reader)),
            Map.entry("Received", text),
            Map.entry("Problem", e.getMessage())
          ),
          "error-layout-descriptor-unparseable",
          Optional.empty()
        );
      }
    }
  }
}
