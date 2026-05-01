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

import com.io7m.calino.api.CLNByteOrder;
import com.io7m.calino.api.CLNChannelsLayoutDescriptionType;
import com.io7m.calino.api.CLNFileWritableType;
import com.io7m.calino.api.CLNImage2DMipMapDeclaration;
import com.io7m.calino.api.CLNImage2DMipMapDeclarations;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.imageproc.api.CLNImageLayoutConversion;
import com.io7m.calino.imageproc.api.CLNImageMipMapChainType;
import com.io7m.calino.imageproc.api.CLNImageMipMapFilter;
import com.io7m.calino.imageproc.api.CLNImageProcessorRequest;
import com.io7m.calino.imageproc.awt.CLNImageProcessorsAWT;
import com.io7m.calino.supercompression.api.CLNCompressorRequest;
import com.io7m.calino.supercompression.api.CLNCompressors;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.calino.writer.api.CLNWriters;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed01;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.quarrel.core.QStringType.QLocalize;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Properties;
import java.util.zip.CRC32;

import static com.io7m.calino.api.CLNByteOrder.LITTLE_ENDIAN;
import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.UNCOMPRESSED;
import static java.lang.Boolean.FALSE;
import static java.lang.Integer.toUnsignedLong;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

/**
 * The 'create-2d' command.
 */

public final class CLNCommandCreate2D extends CLNAbstractCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandCreate2D.class);

  private static final QParameterNamed1<Path> SOURCE =
    new QParameterNamed1<>(
      "--source",
      List.of(),
      new QConstant("The source image file."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed1<Path> OUTPUT =
    new QParameterNamed1<>(
      "--output",
      List.of(),
      new QConstant("The output texture file."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed01<CLNImageMipMapFilter> MIP_MAP_GENERATE =
    new QParameterNamed01<>(
      "--mipmap-generate",
      List.of(),
      new QConstant("The mipmap filter, if mipmaps are to be generated."),
      Optional.empty(),
      CLNImageMipMapFilter.class
    );

  private static final QParameterNamed1<Boolean> PREMULTIPLY_ALPHA =
    new QParameterNamed1<>(
      "--premultiply-alpha",
      List.of(),
      new QConstant("Premultiply alpha."),
      Optional.of(FALSE),
      Boolean.class
    );

  private static final QParameterNamed1<CLNByteOrder> BYTE_ORDER =
    new QParameterNamed1<>(
      "--byte-order",
      List.of(),
      new QConstant("The byte order used for image data."),
      Optional.of(LITTLE_ENDIAN),
      CLNByteOrder.class
    );

  private static final QParameterNamed1<CLNVersion> FORMAT_VERSION =
    new QParameterNamed1<>(
      "--format-version",
      List.of(),
      new QConstant("The requested file format version."),
      Optional.of(new CLNVersion(2, 0)),
      CLNVersion.class
    );

  private static final QParameterNamed01<CLNChannelsLayoutDescriptionType> CONVERT_LAYOUT_TO =
    new QParameterNamed01<>(
      "--convert-layout-to",
      List.of(),
      new QConstant("The requested layout to which to convert."),
      Optional.empty(),
      CLNChannelsLayoutDescriptionType.class
    );

  private static final QParameterNamed1<CLNSuperCompressionMethodType> SUPER_COMPRESSION =
    new QParameterNamed1<>(
      "--super-compression",
      List.of(),
      new QConstant("The super compression method."),
      Optional.of(UNCOMPRESSED),
      CLNSuperCompressionMethodType.class
    );

  private static final QParameterNamed01<Path> METADATA_FILE =
    new QParameterNamed01<>(
      "--metadata",
      List.of(),
      new QConstant(
        "A Java properties file containing metadata for the texture file."),
      Optional.empty(),
      Path.class
    );


  @Override
  protected List<QParameterNamedType<?>> onListNamedParametersActual()
  {
    return List.of(
      BYTE_ORDER,
      CONVERT_LAYOUT_TO,
      FORMAT_VERSION,
      METADATA_FILE,
      MIP_MAP_GENERATE,
      OUTPUT,
      PREMULTIPLY_ALPHA,
      SOURCE,
      SUPER_COMPRESSION
    );
  }

  /**
   * The 'create-2d' command.
   */

  public CLNCommandCreate2D()
  {
    super(
      new QCommandMetadata(
        "create-2d",
        new QConstant("Create a 2D texture from an existing image."),
        Optional.of(new QLocalize("cmd.create2d.helpExt"))
      )
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var writers = new CLNWriters();

    final var formatVersion =
      context.parameterValue(FORMAT_VERSION);
    final var convertLayoutTo =
      context.parameterValue(CONVERT_LAYOUT_TO);
    final var source =
      context.parameterValue(SOURCE);
    final var premultiplyAlpha =
      context.parameterValue(PREMULTIPLY_ALPHA);
    final var byteOrder =
      context.parameterValue(BYTE_ORDER);
    final var mipMapGenerate =
      context.parameterValue(MIP_MAP_GENERATE);
    final var output =
      context.parameterValue(OUTPUT);
    final var metadataFile =
      context.parameterValue(METADATA_FILE);
    final var superCompression =
      context.parameterValue(SUPER_COMPRESSION);

    final var writerOpt =
      writers.findWriterFactoryFor(formatVersion);

    if (writerOpt.isEmpty()) {
      LOG.error("No available writers for format version {}", formatVersion);
      return QCommandStatus.FAILURE;
    }

    final var writerFactory = writerOpt.get();
    final var processors = new CLNImageProcessorsAWT();
    final var compressors = new CLNCompressors();

    try (var resources = CloseableCollection.create()) {
      final var layoutConversion =
        convertLayoutTo.map(CLNImageLayoutConversion::new);

      final var processorRequest =
        new CLNImageProcessorRequest(
          source,
          premultiplyAlpha.booleanValue(),
          byteOrder,
          layoutConversion,
          mipMapGenerate
        );

      final var processor =
        processors.createProcessor(processorRequest);
      final var chain =
        processor.process();

      final var channel =
        resources.add(
          FileChannel.open(output, CREATE, WRITE, TRUNCATE_EXISTING)
        );

      final var request =
        new CLNWriteRequest(channel, output.toUri(), formatVersion);
      final var writer =
        resources.add(writerFactory.createWriter(request));
      final var writable =
        resources.add(writer.execute());

      writeImageInfo(chain, writable, superCompression);
      writeMetadata(writable, metadataFile);
      writeImage2D(compressors, chain, writable, superCompression);
      writeEnd(writable);
    }

    return QCommandStatus.SUCCESS;
  }

  private static void writeMetadata(
    final CLNFileWritableType writable,
    final Optional<Path> metadataFile)
    throws Exception
  {
    if (metadataFile.isPresent()) {
      final var data = openMetadataFile(metadataFile.get());
      try (var section = writable.createSectionMetadata()) {
        section.setMetadata(data);
      }
    }
  }

  private static Map<String, List<String>> openMetadataFile(
    final Path file)
    throws IOException
  {
    try (var stream = Files.newInputStream(file)) {
      final var properties = new Properties();
      properties.load(stream);
      final var data = new HashMap<String, List<String>>(properties.size());
      for (final var entry : properties.entrySet()) {
        data.put((String) entry.getKey(), List.of((String) entry.getValue()));
      }
      return data;
    }
  }

  private static void writeImage2D(
    final CLNCompressors compressors,
    final CLNImageMipMapChainType chain,
    final CLNFileWritableType writable,
    final CLNSuperCompressionMethodType superCompression)
    throws Exception
  {
    try (var section = writable.createSectionImage2D()) {
      final var chainSize =
        chain.mipMapLevelCount();
      final var dataForMipMap =
        new HashMap<CLNImage2DMipMapDeclaration, byte[]>(chainSize);

      /*
       * Create declarations for each level.
       */

      for (var level = chainSize - 1; level >= 0; --level) {
        final var data = chain.mipMapUncompressedBytes(level);

        /*
         * If the data is uncompressed, then add the data to the list
         * directly.
         */

        if (Objects.equals(superCompression, UNCOMPRESSED)) {
          final var crc32 = new CRC32();
          crc32.update(data);

          final var declaration =
            new CLNImage2DMipMapDeclaration(
              level,
              toUnsignedLong(data.length),
              toUnsignedLong(data.length),
              (int) (crc32.getValue() & 0xffff_ffffL)
            );

          dataForMipMap.put(declaration, data);
          continue;
        }

        /*
         * Otherwise, compress the data and add the compressed data to
         * the list.
         */

        final var compressor =
          compressors.createCompressor(
            new CLNCompressorRequest(superCompression)
          );

        final var compressedData =
          compressor.execute(data);

        final var crc32 = new CRC32();
        crc32.update(data);

        final var declaration =
          new CLNImage2DMipMapDeclaration(
            level,
            toUnsignedLong(compressedData.length),
            toUnsignedLong(data.length),
            (int) (crc32.getValue() & 0xffff_ffffL)
          );

        dataForMipMap.put(declaration, compressedData);
      }

      /*
       * For each declaration, write the data for each level. The order
       * that the data is written doesn't matter; the underlying library
       * ensures that the mipmaps are in the correct order.
       */

      final var declarations =
        new CLNImage2DMipMapDeclarations(
          dataForMipMap.keySet()
            .stream()
            .sorted()
            .toList(),
          chain.imageInfo()
            .texelBlockAlignment()
        );

      final var writableMipMaps =
        section.createMipMaps(declarations);

      for (final var declaration : dataForMipMap.keySet()) {
        final var data = dataForMipMap.get(declaration);
        try (var mipChannel =
               writableMipMaps.writeMipMap(declaration.mipMapLevel())) {

          final var r = mipChannel.write(ByteBuffer.wrap(data));
          if (r != data.length) {
            throw new IOException(
              String.format(
                "Expected to write %d bytes but wrote %d",
                Integer.valueOf(data.length),
                Integer.valueOf(r))
            );
          }
        }
      }
    }
  }

  private static void writeEnd(
    final CLNFileWritableType writable)
    throws Exception
  {
    try (var ignored = writable.createSectionEnd()) {
      // Nothing required
    }
  }

  private static void writeImageInfo(
    final CLNImageMipMapChainType chain,
    final CLNFileWritableType writable,
    final CLNSuperCompressionMethodType superCompression)
    throws Exception
  {
    try (var section = writable.createSectionImageInfo()) {
      final var imageInfo = chain.imageInfo();
      final var withCompression = new CLNImageInfo(
        imageInfo.sizeX(),
        imageInfo.sizeY(),
        imageInfo.sizeZ(),
        imageInfo.channelsLayout(),
        imageInfo.channelsType(),
        imageInfo.compressionMethod(),
        superCompression,
        imageInfo.coordinateSystem(),
        imageInfo.colorSpace(),
        imageInfo.flags(),
        imageInfo.dataByteOrder()
      );
      section.setImageInfo(withCompression);
    }
  }
}
