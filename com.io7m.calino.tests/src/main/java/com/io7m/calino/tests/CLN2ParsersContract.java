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
import com.io7m.calino.api.CLNException;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.api.CLNSectionReadableImageCubeType;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableMetadataType;
import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.parser.api.CLNParseRequestBuilderType;
import com.io7m.calino.parser.api.CLNParserType;
import com.io7m.calino.vanilla.CLN2Parsers;
import com.io7m.entomos.core.EoFileSection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.jmulticlose.core.ClosingResourceFailedException;
import com.io7m.junreachable.UnreachableCodeException;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.file.Path;
import java.util.Collection;
import java.util.List;
import java.util.NavigableSet;
import java.util.function.Consumer;
import java.util.zip.CRC32;

import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8_A8;
import static com.io7m.calino.api.CLNChannelsTypeDescriptionStandard.FIXED_POINT_NORMALIZED_UNSIGNED;
import static com.io7m.calino.api.CLNColorSpaceStandard.COLOR_SPACE_SRGB;
import static com.io7m.calino.api.CLNCoordinateAxisR.AXIS_R_INCREASING_TOWARD;
import static com.io7m.calino.api.CLNCoordinateAxisS.AXIS_S_INCREASING_RIGHT;
import static com.io7m.calino.api.CLNCoordinateAxisT.AXIS_T_INCREASING_DOWN;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public abstract class CLN2ParsersContract
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN2ParsersContract.class);

  protected Path directory;
  protected CLN2Parsers parsers;
  protected CloseableCollectionType<ClosingResourceFailedException> resources;

  private static void showSections(
    final Collection<EoFileSection> sections)
  {
    int index = 0;
    for (final var section : sections) {
      LOG.debug(
        "[{}] Section @0x{} 0x{} size {}",
        Integer.valueOf(index),
        Long.toUnsignedString(section.offset(), 16),
        Long.toUnsignedString(section.tag(), 16),
        Long.toUnsignedString(section.dataSize())
      );
      ++index;
    }
  }

  private static EoFileSection sectionGet(
    final NavigableSet<EoFileSection> sections,
    final int r)
  {
    int index = 0;
    for (final var section : sections) {
      if (index == r) {
        return section;
      }
      ++index;
    }
    throw new UnreachableCodeException();
  }

  @Test
  public void testBrokenTruncated()
    throws Exception
  {
    final var parser =
      this.parserFor("broken-truncated.ctf");

    final var ex =
      assertThrows(
        CLNException.class,
        () -> this.resources.add(parser.execute()));
    assertEquals("error-file-tag-missing", ex.errorCode());
    assertEquals("Missing file tag.", ex.getMessage());
  }

  @Test
  public void testBrokenBadIdentifier()
    throws Exception
  {
    final var parser =
      this.parserFor("broken-bad-identifier.ctf");

    final var ex =
      assertThrows(
        CLNException.class,
        () -> this.resources.add(parser.execute()));
    assertEquals("error-file-tag-incorrect", ex.errorCode());
  }

  @Test
  public void testBrokenBadUnsupportedVersion()
    throws Exception
  {
    final var parser =
      this.parserFor("broken-unsupported-version.ctf");

    final var ex =
      assertThrows(
        CLNException.class,
        () -> this.resources.add(parser.execute()));
    assertEquals("error-file-version-not-supported", ex.errorCode());
    assertEquals("File format version is not supported.", ex.getMessage());
  }

  @Test
  public void testBrokenLayoutDescriptor0()
    throws Exception
  {
    final var parser =
      this.parserFor("fade32-broken-layout-descriptor-0.ctf");
    final var file =
      this.resources.add(parser.execute());
    final var section =
      (CLNSectionReadableImageInfoType)
        this.resources.add(file.openSection(file.sections().first()));

    final var ex = assertThrows(CLNException.class, section::info);
    assertEquals("error-layout-descriptor-unparseable", ex.errorCode());
  }

  @Test
  public void testBrokenLayoutDescriptor1()
    throws Exception
  {
    final var parser =
      this.parserFor("fade32-broken-layout-descriptor-1.ctf");
    final var file =
      this.resources.add(parser.execute());
    final var section =
      (CLNSectionReadableImageInfoType)
        this.resources.add(file.openSection(file.sections().first()));

    final var ex = assertThrows(CLNException.class, section::info);
    assertEquals("error-layout-descriptor-unparseable", ex.errorCode());
  }

  @Test
  public void testEmpty()
    throws Exception
  {
    final var parser =
      this.parserFor("empty.ctf");

    final var ex =
      assertThrows(CLNException.class, () -> {
        this.resources.add(parser.execute());
      });

    assertEquals("error-section-tag-first", ex.errorCode());
    assertEquals("The first section is not of the required tag.", ex.getMessage());
  }

  @Test
  public void testBasicImageInfo()
    throws Exception
  {
    final var parser =
      this.parserFor("fade32.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType)
             file.openSection(sections.first())) {
      final var info = section.info();
      assertEquals(32, info.sizeX());
      assertEquals(32, info.sizeY());
      assertEquals(1, info.sizeZ());
      assertEquals(R8_G8_B8_A8, info.channelsLayout());
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
  }

  @Test
  public void testBasicImageInfoDescriptorLimit0()
    throws Exception
  {
    /*
     * Set a limit that will cause an exception whilst parsing the
     * channel layout descriptor.
     */

    final var parser =
      this.parserFor("fade32.ctf", builder -> {
        builder.setDescriptorLengthLimit(1L);
      });
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType) file.openSection(
             sections.first())) {
      final var ex = assertThrows(CLNException.class, section::info);
      assertEquals("error-limit-exceeded", ex.errorCode());
      assertTrue(ex.getMessage().contains("Limit exceeded."));
    }
  }

  @Test
  public void testBasicImageInfoDescriptorLimit1()
    throws Exception
  {
    /*
     * Set a limit that will cause an exception whilst parsing the
     * channel type.
     */

    final var parser =
      this.parserFor("fade32.ctf", builder -> {
        builder.setDescriptorLengthLimit(3L);
      });
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType) file.openSection(
             sections.first())) {
      final var ex = assertThrows(CLNException.class, section::info);
      assertEquals("error-limit-exceeded", ex.errorCode());
    }
  }

  @Test
  public void testBasicImageInfoDescriptorLimit2()
    throws Exception
  {
    /*
     * Set a limit that will cause an exception whilst parsing the
     * compression descriptor.
     */

    final var parser =
      this.parserFor("fade32.ctf", builder -> {
        builder.setDescriptorLengthLimit(7L);
      });
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType) file.openSection(
             sections.first())) {
      final var ex = assertThrows(CLNException.class, section::info);
      assertEquals("error-limit-exceeded", ex.errorCode());
    }
  }

  @Test
  public void testBasicImageInfoDescriptorLimit3()
    throws Exception
  {
    /*
     * Set a limit that will cause an exception whilst parsing the
     * supercompression descriptor.
     */

    final var parser =
      this.parserFor("fade32.ctf", builder -> {
        builder.setDescriptorLengthLimit(9L);
      });
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImageInfoType) file.openSection(
             sections.first())) {
      final var ex = assertThrows(CLNException.class, section::info);
      assertEquals("error-limit-exceeded", ex.errorCode());
    }
  }

  @Test
  public void testBasicMetadata()
    throws Exception
  {
    final var parser =
      this.parserFor("fade32.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableMetadataType) file.openSection(
             sectionGet(sections,1))) {
      final var metadata = section.metadata();
      LOG.debug("metadata: {}", metadata);
      assertEquals(3, metadata.size());
      assertEquals(List.of("Public Domain"), metadata.get("dc.rights"));
      assertEquals(List.of("f9c2cf13-8919-4cfd-b88f-0a6c9e552d59"), metadata.get("dc.identifier"));
      assertEquals(List.of("Fade32"), metadata.get("dc.title"));
    }
  }

  @Test
  public void testBasicMetadataLimit()
    throws Exception
  {
    final var parser =
      this.parserFor("fade32.ctf", builder -> {
        builder.setKeyValueDatumLimit(1L);
      });
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableMetadataType)
             file.openSection(sectionGet(sections,1))) {
      final var ex =
        assertThrows(IOException.class, section::metadata);
      assertTrue(ex.getMessage().contains("Limit exceeded."));
    }
  }

  @Test
  public void testBasicImage2D()
    throws Exception
  {
    final var parser =
      this.parserFor("fade32.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImage2DType) file.openSection(sectionGet(sections,2))) {
      final var mipmaps = section.mipMapDescriptions();
      LOG.debug("mipmaps: {}", mipmaps);
      assertEquals(1, mipmaps.size());
      final var map0 = mipmaps.get(0);
      final var crc32Declared = map0.crc32Uncompressed();
      assertEquals(0xcc4dd15c, crc32Declared);
      assertEquals(64L, map0.dataOffsetWithinSection());
      assertEquals(4096L, map0.dataSizeCompressed());
      assertEquals(4096L, map0.dataSizeUncompressed());
      assertEquals(0, map0.mipMapLevel());

      try (var channel = section.mipMapDataWithoutSupercompression(map0)) {
        final var buffer = new byte[(int) map0.dataSizeUncompressed()];
        final var byteBuffer = ByteBuffer.wrap(buffer);
        final var read = channel.read(byteBuffer);
        assertEquals(4096L, read);

        final var crc32 = new CRC32();
        crc32.reset();
        crc32.update(buffer);
        final int crc32Received = (int) crc32.getValue();

        LOG.debug(
          "crc32 declared: 0x{}",
          Integer.toUnsignedString(crc32Declared, 16));
        LOG.debug(
          "crc32 received: 0x{}",
          Integer.toUnsignedString(crc32Received, 16));

        assertEquals(crc32Declared, crc32Received);
      }
    }
  }

  @Test
  public void testBasicImage2DLZ4()
    throws Exception
  {
    final var parser =
      this.parserFor("fade32-lz4.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImage2DType) file.openSection(sectionGet(sections,2))) {
      final var mipmaps = section.mipMapDescriptions();
      LOG.debug("mipmaps: {}", mipmaps);
      assertEquals(1, mipmaps.size());
      final var map0 = mipmaps.get(0);
      final var crc32Declared = map0.crc32Uncompressed();
      assertEquals(0xcc4dd15c, crc32Declared);
      assertEquals(64L, map0.dataOffsetWithinSection());
      assertEquals(2789L, map0.dataSizeCompressed());
      assertEquals(4096L, map0.dataSizeUncompressed());
      assertEquals(0, map0.mipMapLevel());

      try (var channel = section.mipMapDataWithoutSupercompression(map0)) {
        final var buffer = new byte[(int) map0.dataSizeUncompressed()];
        final var byteBuffer = ByteBuffer.wrap(buffer);

        var read = 0;
        while (read != 4096) {
          read += channel.read(byteBuffer);
        }
        assertEquals(4096, read);

        final var crc32 = new CRC32();
        crc32.reset();
        crc32.update(buffer);
        final int crc32Received = (int) crc32.getValue();

        LOG.debug(
          "crc32 declared: 0x{}",
          Integer.toUnsignedString(crc32Declared, 16));
        LOG.debug(
          "crc32 received: 0x{}",
          Integer.toUnsignedString(crc32Received, 16));

        assertEquals(crc32Declared, crc32Received);
      }
    }
  }

  @Test
  public void testBasicImage2DLZ4Dump0()
    throws Exception
  {
    final var parser =
      this.parserFor("fade32-lz4.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImage2DType) file.openSection(sectionGet(sections,2))) {
      final var mipmaps = section.mipMapDescriptions();
      final var map0 = mipmaps.get(0);

      try (var channel = section.mipMapDataRaw(map0)) {
        final var buffer = new byte[(int) map0.dataSizeCompressed()];
        final var byteBuffer = ByteBuffer.wrap(buffer);
        channel.read(byteBuffer);

        final var text = new StringBuilder(128);
        for (int index = 0; index < buffer.length; ++index) {
          text.append(String.format("%02x", Byte.valueOf(buffer[index])));
          if ((index + 1) % 16 == 0) {
            text.append('\n');
          } else if ((index + 1) % 4 == 0) {
            text.append(' ');
          }
        }

        System.out.println(text);
      }
    }
  }

  @Test
  public void testBasicImage2DUnknownDescription0()
    throws Exception
  {
    final var parser =
      this.parserFor("fade32.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(4, sections.size());

    try (var section =
           (CLNSectionReadableImage2DType) file.openSection(sectionGet(sections,2))) {
      assertThrows(CLNException.class, () -> {
        section.mipMapDataWithoutSupercompression(new CLNImage2DDescription(
          23,
          0L,
          100L,
          200L,
          0
        ));
      });
      assertThrows(CLNException.class, () -> {
        section.mipMapDataRaw(new CLNImage2DDescription(
          23,
          0L,
          100L,
          200L,
          0
        ));
      });
    }
  }

  @Test
  public void testBasicImageCube()
    throws Exception
  {
    final var parser =
      this.parserFor("cube-mipmaps.ctf");
    final var file =
      this.resources.add(parser.execute());

    assertEquals(new CLNVersion(2, 0), file.version());

    final var sections = file.sections();
    showSections(sections);
    assertEquals(3, sections.size());

    try (var section =
           (CLNSectionReadableImageCubeType) file.openSection(sectionGet(sections,1))) {
      final var mipmaps = section.mipMapDescriptions();
      LOG.debug("mipmaps: {}", mipmaps);
      assertEquals(48, mipmaps.size());
      final var map0 = mipmaps.get(0);
      final var crc32Declared = map0.crc32Uncompressed();
      assertEquals(0x8332c492, crc32Declared);
      assertEquals(1408L, map0.dataOffsetWithinSection());
      assertEquals(16L, map0.dataSizeCompressed());
      assertEquals(16L, map0.dataSizeUncompressed());
      assertEquals(7, map0.mipMapLevel());

      try (var channel = section.mipMapDataWithoutSupercompression(map0)) {
        final var buffer = new byte[(int) map0.dataSizeUncompressed()];
        final var byteBuffer = ByteBuffer.wrap(buffer);
        final var read = channel.read(byteBuffer);
        assertEquals(16, read);

        final var crc32 = new CRC32();
        crc32.reset();
        crc32.update(buffer);
        final int crc32Received = (int) crc32.getValue();

        LOG.debug(
          "crc32 declared: 0x{}",
          Integer.toUnsignedString(crc32Declared, 16));
        LOG.debug(
          "crc32 received: 0x{}",
          Integer.toUnsignedString(crc32Received, 16));

        assertEquals(crc32Declared, crc32Received);
      }
    }
  }

  protected final CLNParserType parserFor(
    final String name)
    throws Exception
  {
    return this.parserFor(name, builder -> {
    });
  }

  protected abstract CLNParserType parserFor(
    String name,
    Consumer<CLNParseRequestBuilderType> configurator)
    throws Exception;
}
