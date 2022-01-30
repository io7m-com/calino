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

import com.io7m.calino.api.CLNByteOrder;
import com.io7m.calino.api.CLNColorSpaceStandard;
import com.io7m.calino.api.CLNCompressionMethodStandard;
import com.io7m.calino.api.CLNCoordinateAxisR;
import com.io7m.calino.api.CLNCoordinateAxisS;
import com.io7m.calino.api.CLNCoordinateAxisT;
import com.io7m.calino.api.CLNCoordinateSystem;
import com.io7m.calino.api.CLNImage2DMipMapDeclaration;
import com.io7m.calino.api.CLNImage2DMipMapDeclarations;
import com.io7m.calino.api.CLNImageFlagStandard;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableMetadataType;
import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParsers;
import com.io7m.calino.supercompression.api.CLNDecompressors;
import com.io7m.calino.vanilla.CLN1Writers;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.jmulticlose.core.CloseableCollection;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.ByteBuffer;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8;
import static com.io7m.calino.api.CLNChannelsTypeDescriptionStandard.FIXED_POINT_NORMALIZED_UNSIGNED;
import static com.io7m.calino.api.CLNCoordinateAxisR.*;
import static com.io7m.calino.api.CLNCoordinateAxisS.*;
import static com.io7m.calino.api.CLNCoordinateAxisT.*;
import static com.io7m.calino.api.CLNImageFlagStandard.ALPHA_PREMULTIPLIED;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.READ;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;
import static java.util.Map.entry;
import static java.util.Map.ofEntries;

public final class CLNWriteDemo
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNWriteDemo.class);

  private CLNWriteDemo()
  {

  }

  public static void main(
    final String[] args)
    throws Exception
  {
    final var writers =
      new CLN1Writers();
    final var parsers =
      new CLNParsers();

    final var path =
      Paths.get("/tmp/out.ctf");

    try (var resources = CloseableCollection.create()) {
      final var channel =
        resources.add(Files.newByteChannel(
          path,
          TRUNCATE_EXISTING,
          CREATE,
          WRITE));

      final var request =
        new CLNWriteRequest(channel, path.toUri(), new CLNVersion(1, 0));
      final var writer =
        resources.add(writers.createWriter(request));
      final var writable =
        resources.add(writer.execute());

      try (var section = writable.createSectionImageInfo()) {
        section.setImageInfo(
          new CLNImageInfo(
            32,
            32,
            1,
            R8_G8_B8,
            FIXED_POINT_NORMALIZED_UNSIGNED,
            CLNCompressionMethodStandard.UNCOMPRESSED,
            CLNSuperCompressionMethodStandard.UNCOMPRESSED,
            new CLNCoordinateSystem(
              AXIS_R_INCREASING_TOWARD,
              AXIS_S_INCREASING_RIGHT,
              AXIS_T_INCREASING_DOWN
            ),
            CLNColorSpaceStandard.COLOR_SPACE_SRGB,
            Set.of(ALPHA_PREMULTIPLIED),
            CLNByteOrder.LITTLE_ENDIAN
          )
        );
      }

      try (var section = writable.createSectionMetadata()) {
        section.setMetadata(
          ofEntries(
            entry("key0", List.of("value0")),
            entry("key1", List.of("value1")),
            entry("key2", List.of("value2")),
            entry("key3", List.of("value3")),
            entry("key4", List.of("value4")),
            entry("key5", List.of("value5")),
            entry("key6", List.of("value6")),
            entry("key7", List.of("value7")),
            entry("key8", List.of("value8")),
            entry("key9", List.of("value9"))
          )
        );
      }

      try (var section = writable.createSectionImage2D()) {
        final var mipMaps =
          section.createMipMaps(new CLNImage2DMipMapDeclarations(
            List.of(
              new CLNImage2DMipMapDeclaration(
                0,
                3072L,
                3072L,
                0xf5b99b42
              ),
              new CLNImage2DMipMapDeclaration(
                1,
                768L,
                768L,
                0xeb2f11db
              ),
              new CLNImage2DMipMapDeclaration(
                2,
                192L,
                192L,
                0x4e8fd525
              ),
              new CLNImage2DMipMapDeclaration(
                3,
                48L,
                48L,
                0xe0ed553c
              ),
              new CLNImage2DMipMapDeclaration(
                4,
                12L,
                12L,
                0xadf413fd
              )
            ),
            4
          ));

        for (int mipMapLevel = 0; mipMapLevel <= 4; ++mipMapLevel) {
          try (var mip = mipMaps.writeMipMap(mipMapLevel)) {
            final var width = 32 >> mipMapLevel;
            final var size = (width * 3) * width;
            final var data = new byte[size];
            Arrays.fill(data, (byte) (0x41 + mipMapLevel));
            final var dataBuffer = ByteBuffer.wrap(data);
            mip.write(dataBuffer);
          }
        }
      }

      try (var section = writable.createSectionEnd()) {

      }
    }

    try (var resources = CloseableCollection.create()) {
      final var channel =
        resources.add(Files.newByteChannel(path, READ));

      final var request =
        CLNParseRequest.builder(new CLNDecompressors(), channel, path.toUri())
          .build();

      final var reader =
        resources.add(parsers.createParser(request));
      final var readable =
        resources.add(reader.execute());

      for (final var section : readable.sections()) {
        try (var sectionReader = readable.openSection(section)) {
          if (sectionReader instanceof CLNSectionReadableMetadataType metadata) {
            LOG.debug("metadata: {}", metadata.metadata());
            continue;
          }
          if (sectionReader instanceof CLNSectionReadableImageInfoType imageInfo) {
            LOG.debug("imageInfo: {}", imageInfo.info());
            continue;
          }
        }
      }
    }
  }
}
