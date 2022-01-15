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

package com.io7m.calino.tests;

import com.io7m.calino.api.CLNCompressionMethodStandard;
import com.io7m.calino.api.CLNCoordinateAxisR;
import com.io7m.calino.api.CLNCoordinateAxisS;
import com.io7m.calino.api.CLNCoordinateAxisT;
import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNSectionReadableEndType;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableMetadataType;
import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.parser.api.CLNParseRequestBuilderType;
import com.io7m.calino.parser.api.CLNParserType;
import com.io7m.calino.parser.api.CLNParserValidationEvent;
import com.io7m.calino.vanilla.CLN1Parsers;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.jmulticlose.core.ClosingResourceFailedException;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.zip.CRC32;

import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8;
import static com.io7m.calino.api.CLNChannelsTypeDescriptionStandard.FIXED_POINT_NORMALIZED_UNSIGNED;
import static com.io7m.calino.api.CLNColorSpaceStandard.COLOR_SPACE_SRGB;
import static com.io7m.calino.api.CLNCoordinateAxisR.*;
import static com.io7m.calino.api.CLNCoordinateAxisS.*;
import static com.io7m.calino.api.CLNCoordinateAxisT.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public abstract class CLN1ParsersContract
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN1ParsersContract.class);

  protected Path directory;
  protected CLN1Parsers parsers;
  protected CloseableCollectionType<ClosingResourceFailedException> resources;
  protected ArrayList<CLNParserValidationEvent> events;

  private static void showSections(
    final List<CLNFileSectionDescription> sections)
  {
    for (int index = 0; index < sections.size(); ++index) {
      final var section = sections.get(index);
      LOG.debug(
        "[{}] Section @0x{} 0x{} size {}",
        Integer.valueOf(index),
        Long.toUnsignedString(section.fileOffset(), 16),
        Long.toUnsignedString(section.description().identifier(), 16),
        Long.toUnsignedString(section.description().size())
      );
    }
  }

  @Test
  public void testBrokenTruncated()
    throws IOException
  {
    final var parser =
      this.parserFor("broken-truncated.ctf");

    final var ex =
    assertThrows(IOException.class, () -> this.resources.add(parser.execute()));
    assertTrue(ex.getMessage().contains("Out of bounds."));
  }

  @Test
  public void testBrokenBadIdentifier()
    throws IOException
  {
    final var parser =
      this.parserFor("broken-bad-identifier.ctf");

    final var ex =
      assertThrows(IOException.class, () -> this.resources.add(parser.execute()));
    assertTrue(ex.getMessage().contains("Unrecognized file identifier."));
  }

  @Test
  public void testBrokenBadUnsupportedVersion()
    throws IOException
  {
    final var parser =
      this.parserFor("broken-unsupported-version.ctf");

    final var ex =
      assertThrows(IOException.class, () -> this.resources.add(parser.execute()));
    assertTrue(ex.getMessage().contains("Unrecognized major version."));
  }

  @Test
  public void testBrokenLayoutDescriptor0()
    throws IOException
  {
    final var parser =
      this.parserFor("broken-layout-descriptor-0.ctf");
    final var file =
      this.resources.add(parser.execute());
    final var section =
      (CLNSectionReadableImageInfoType)
        this.resources.add(file.openSection(file.sections().get(0)));

    assertThrows(IOException.class, section::info);
  }

  @Test
  public void testBrokenLayoutDescriptor1()
    throws IOException
  {
    final var parser =
      this.parserFor("broken-layout-descriptor-1.ctf");
    final var file =
      this.resources.add(parser.execute());
    final var section =
      (CLNSectionReadableImageInfoType)
        this.resources.add(file.openSection(file.sections().get(0)));

    assertThrows(IOException.class, section::info);
  }

  @Test
  public void testEmpty()
    throws IOException
  {
    final var parser =
      this.parserFor("empty.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(1, sections.size());

    {
      final var fileSectionDescription =
        sections.get(0);
      final var sectionDescription =
        fileSectionDescription.description();

      assertEquals(
        CLNIdentifiers.sectionEndIdentifier(),
        sectionDescription.identifier()
      );

      try (var end = (CLNSectionReadableEndType)
        file.openSection(fileSectionDescription)) {

        try (var channel = end.sectionDataChannel()) {
          assertEquals(0L, channel.size());
        }
      }
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicImageInfo()
    throws IOException
  {
    final var parser =
      this.parserFor("basic.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType)
             file.openSection(sections.get(0))) {
      final var info = section.info();
      assertEquals(32, info.sizeX());
      assertEquals(32, info.sizeY());
      assertEquals(1, info.sizeZ());
      assertEquals(R8_G8_B8, info.channelsLayout());
      assertEquals(FIXED_POINT_NORMALIZED_UNSIGNED, info.channelsType());
      assertEquals(
        CLNCompressionMethodStandard.UNCOMPRESSED,
        info.compressionMethod());
      assertEquals(
        CLNSuperCompressionMethodStandard.UNCOMPRESSED,
        info.superCompressionMethod());
      assertEquals(AXIS_R_INCREASING_TOWARD, info.coordinateSystem().axisR());
      assertEquals(AXIS_S_INCREASING_RIGHT, info.coordinateSystem().axisS());
      assertEquals(AXIS_T_INCREASING_DOWN, info.coordinateSystem().axisT());
      assertEquals(COLOR_SPACE_SRGB, info.colorSpace());
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicImageInfoDescriptorLimit0()
    throws IOException
  {
    /*
     * Set a limit that will cause an exception whilst parsing the
     * channel layout descriptor.
     */

    final var parser =
      this.parserFor("basic.ctf", builder -> {
        builder.setDescriptorLengthLimit(1L);
      });
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType) file.openSection(
             sections.get(0))) {
      final var ex =
        assertThrows(IOException.class, section::info);
      assertTrue(ex.getMessage().contains("Limit exceeded."));
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicImageInfoDescriptorLimit1()
    throws IOException
  {
    /*
     * Set a limit that will cause an exception whilst parsing the
     * channel type.
     */

    final var parser =
      this.parserFor("basic.ctf", builder -> {
        builder.setDescriptorLengthLimit(3L);
      });
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType) file.openSection(
             sections.get(0))) {
      final var ex =
        assertThrows(IOException.class, section::info);
      LOG.debug("ex: ", ex);
      assertTrue(ex.getMessage().contains("Limit exceeded."));
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicImageInfoDescriptorLimit2()
    throws IOException
  {
    /*
     * Set a limit that will cause an exception whilst parsing the
     * compression descriptor.
     */

    final var parser =
      this.parserFor("basic.ctf", builder -> {
        builder.setDescriptorLengthLimit(7L);
      });
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType) file.openSection(
             sections.get(0))) {
      final var ex =
        assertThrows(IOException.class, section::info);
      LOG.debug("ex: ", ex);
      assertTrue(ex.getMessage().contains("Limit exceeded."));
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicImageInfoDescriptorLimit3()
    throws IOException
  {
    /*
     * Set a limit that will cause an exception whilst parsing the
     * supercompression descriptor.
     */

    final var parser =
      this.parserFor("basic.ctf", builder -> {
        builder.setDescriptorLengthLimit(9L);
      });
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType) file.openSection(
             sections.get(0))) {
      final var ex =
        assertThrows(IOException.class, section::info);
      LOG.debug("ex: ", ex);
      assertTrue(ex.getMessage().contains("Limit exceeded."));
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicMetadata()
    throws IOException
  {
    final var parser =
      this.parserFor("basic.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableMetadataType) file.openSection(
             sections.get(1))) {
      final var metadata = section.metadata();
      LOG.debug("metadata: {}", metadata);
      assertEquals(2, metadata.size());
      assertEquals("VAL0", metadata.get("K0"));
      assertEquals("VAL1", metadata.get("KEY1"));
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicMetadataLimit()
    throws IOException
  {
    final var parser =
      this.parserFor("basic.ctf", builder -> {
        builder.setKeyValueDatumLimit(1L);
      });
    final var file =
      this.resources.add(parser.execute());
    
    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableMetadataType)
             file.openSection(sections.get(1))) {
      final var ex =
        assertThrows(IOException.class, section::metadata);
      assertTrue(ex.getMessage().contains("Limit exceeded."));
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicImage2D()
    throws IOException
  {
    final var parser =
      this.parserFor("basic.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImage2DType) file.openSection(sections.get(2))) {
      final var mipmaps = section.mipMapDescriptions();
      LOG.debug("mipmaps: {}", mipmaps);
      assertEquals(1, mipmaps.size());
      final var map0 = mipmaps.get(0);
      final var crc32Declared = map0.crc32Uncompressed();
      assertEquals(0xf3afeedf, crc32Declared);
      assertEquals(48L, map0.dataOffsetWithinSection());
      assertEquals(3072L, map0.dataSizeCompressed());
      assertEquals(3072L, map0.dataSizeUncompressed());
      assertEquals(0, map0.mipMapLevel());

      try (var channel = section.mipMapDataWithoutSupercompression(map0)) {
        final var buffer = new byte[(int) map0.dataSizeUncompressed()];
        final var byteBuffer = ByteBuffer.wrap(buffer);
        final var read = channel.read(byteBuffer);
        assertEquals(3072, read);

        final var crc32 = new CRC32();
        crc32.reset();
        crc32.update(buffer);
        final int crc32Received = (int) crc32.getValue();

        LOG.debug("crc32 declared: 0x{}",
                  Integer.toUnsignedString(crc32Declared, 16));
        LOG.debug("crc32 received: 0x{}",
                  Integer.toUnsignedString(crc32Received, 16));

        assertEquals(crc32Declared, crc32Received);
      }
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicImage2DLZ4()
    throws IOException
  {
    final var parser =
      this.parserFor("basic-lz4.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImage2DType) file.openSection(sections.get(2))) {
      final var mipmaps = section.mipMapDescriptions();
      LOG.debug("mipmaps: {}", mipmaps);
      assertEquals(1, mipmaps.size());
      final var map0 = mipmaps.get(0);
      final var crc32Declared = map0.crc32Uncompressed();
      assertEquals(0xf3afeedf, crc32Declared);
      assertEquals(48L, map0.dataOffsetWithinSection());
      assertEquals(2094L, map0.dataSizeCompressed());
      assertEquals(3072L, map0.dataSizeUncompressed());
      assertEquals(0, map0.mipMapLevel());

      try (var channel = section.mipMapDataWithoutSupercompression(map0)) {
        final var buffer = new byte[(int) map0.dataSizeUncompressed()];
        final var byteBuffer = ByteBuffer.wrap(buffer);

        var read = 0;
        while (read != 3072) {
          read += channel.read(byteBuffer);
        }
        assertEquals(3072, read);

        final var crc32 = new CRC32();
        crc32.reset();
        crc32.update(buffer);
        final int crc32Received = (int) crc32.getValue();

        LOG.debug("crc32 declared: 0x{}",
                  Integer.toUnsignedString(crc32Declared, 16));
        LOG.debug("crc32 received: 0x{}",
                  Integer.toUnsignedString(crc32Received, 16));

        assertEquals(crc32Declared, crc32Received);
      }
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testBasicImage2DUnknownDescription0()
    throws IOException
  {
    final var parser =
      this.parserFor("basic.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImage2DType) file.openSection(sections.get(2))) {
      assertThrows(IllegalArgumentException.class, () -> {
        section.mipMapDataWithoutSupercompression(new CLNImage2DDescription(
          23,
          0L,
          100L,
          200L,
          0
        ));
      });
      assertThrows(IllegalArgumentException.class, () -> {
        section.mipMapDataRaw(new CLNImage2DDescription(
          23,
          0L,
          100L,
          200L,
          0
        ));
      });
    }

    assertEquals(0, this.events.size());
  }

  @Test
  public void testWarnUnaligned()
    throws IOException
  {
    final var parser =
      this.parserFor("warn-unaligned.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(3, sections.size());

    assertEquals(2, this.events.size());
    assertTrue(this.events.remove(0).message().contains("not aligned"));
    assertTrue(this.events.remove(0).message().contains("not aligned"));
  }


  @Test
  public void testWarnTrailing()
    throws IOException
  {
    final var parser =
      this.parserFor("warn-trailing.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(1, sections.size());

    assertEquals(1, this.events.size());
    assertTrue(this.events.remove(0).message().contains("trailing data"));
  }

  @Test
  public void testWarnEndNonzero()
    throws IOException
  {
    final var parser =
      this.parserFor("warn-end-nonzero.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(1, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(1, sections.size());

    assertEquals(1, this.events.size());
    assertTrue(this.events.remove(0).message().contains("non-zero size"));
  }

  protected final CLNParserType parserFor(
    final String name)
    throws IOException
  {
    return this.parserFor(name, builder -> {});
  }

  protected abstract CLNParserType parserFor(
    String name,
    Consumer<CLNParseRequestBuilderType> configurator)
    throws IOException;
}
