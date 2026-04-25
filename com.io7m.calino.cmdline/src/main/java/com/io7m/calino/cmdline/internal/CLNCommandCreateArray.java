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
import com.io7m.calino.api.CLNImageArrayMipMapDeclaration;
import com.io7m.calino.api.CLNImageArrayMipMapDeclarations;
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
import com.io7m.jmulticlose.core.ClosingResourceFailedException;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed01;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamed1N;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Properties;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.zip.CRC32;

import static com.io7m.calino.api.CLNByteOrder.LITTLE_ENDIAN;
import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.UNCOMPRESSED;
import static java.lang.Boolean.FALSE;
import static java.lang.Integer.toUnsignedLong;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

/**
 * The 'create-array' command.
 */

public final class CLNCommandCreateArray extends CLNAbstractCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandCreateArray.class);

  private static final QParameterNamed1N<Path> LAYERS =
    new QParameterNamed1N<>(
      "--source-layer",
      List.of(),
      new QStringType.QConstant(
        "The source image layer files, in layer order starting at 0."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed1<Path> OUTPUT =
    new QParameterNamed1<>(
      "--output",
      List.of(),
      new QStringType.QConstant("The output texture file."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed01<CLNImageMipMapFilter> MIP_MAP_GENERATE =
    new QParameterNamed01<>(
      "--mipmap-generate",
      List.of(),
      new QStringType.QConstant(
        "The mipmap filter, if mipmaps are to be generated."),
      Optional.empty(),
      CLNImageMipMapFilter.class
    );

  private static final QParameterNamed1<Boolean> PREMULTIPLY_ALPHA =
    new QParameterNamed1<>(
      "--premultiply-alpha",
      List.of(),
      new QStringType.QConstant("Premultiply alpha."),
      Optional.of(FALSE),
      Boolean.class
    );

  private static final QParameterNamed1<CLNByteOrder> BYTE_ORDER =
    new QParameterNamed1<>(
      "--byte-order",
      List.of(),
      new QStringType.QConstant("The byte order used for image data."),
      Optional.of(LITTLE_ENDIAN),
      CLNByteOrder.class
    );

  private static final QParameterNamed1<CLNVersion> FORMAT_VERSION =
    new QParameterNamed1<>(
      "--format-version",
      List.of(),
      new QStringType.QConstant("The requested file format version."),
      Optional.of(new CLNVersion(1, 0)),
      CLNVersion.class
    );

  private static final QParameterNamed01<CLNChannelsLayoutDescriptionType> CONVERT_LAYOUT_TO =
    new QParameterNamed01<>(
      "--convert-layout-to",
      List.of(),
      new QStringType.QConstant("The requested layout to which to convert."),
      Optional.empty(),
      CLNChannelsLayoutDescriptionType.class
    );

  private static final QParameterNamed1<CLNSuperCompressionMethodType> SUPER_COMPRESSION =
    new QParameterNamed1<>(
      "--super-compression",
      List.of(),
      new QStringType.QConstant("The super compression method."),
      Optional.of(UNCOMPRESSED),
      CLNSuperCompressionMethodType.class
    );

  private static final QParameterNamed01<Path> METADATA_FILE =
    new QParameterNamed01<>(
      "--metadata",
      List.of(),
      new QStringType.QConstant(
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
      LAYERS,
      METADATA_FILE,
      MIP_MAP_GENERATE,
      OUTPUT,
      PREMULTIPLY_ALPHA,
      SUPER_COMPRESSION
    );
  }

  /**
   * The 'create-array' command.
   */

  public CLNCommandCreateArray()
  {
    super(
      new QCommandMetadata(
        "create-array",
        new QStringType.QConstant(
          "Create an array texture from an existing image."),
        Optional.of(new QStringType.QLocalize("cmd.create-array.helpExt"))
      )
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws IOException, ClosingResourceFailedException
  {
    final var writers = new CLNWriters();

    final var formatVersion =
      context.parameterValue(FORMAT_VERSION);
    final var convertLayoutTo =
      context.parameterValue(CONVERT_LAYOUT_TO);
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
    final var layers =
      context.parameterValues(LAYERS);

    final var writerOpt =
      writers.findWriterFactoryFor(formatVersion);

    if (writerOpt.isEmpty()) {
      LOG.error(
        "No available writers for format version {}",
        formatVersion);
      return QCommandStatus.FAILURE;
    }

    if (layers.isEmpty()) {
      LOG.error("At least one image source file is required");
      return QCommandStatus.FAILURE;
    }

    final var writerFactory = writerOpt.get();
    final var processors = new CLNImageProcessorsAWT();
    final var compressors = new CLNCompressors();

    try (var resources = CloseableCollection.create()) {
      final var imageInfos =
        new HashSet<CLNImageInfo>();
      final var chainsForLayers =
        new TreeMap<Integer, CLNImageMipMapChainType>();

      for (int layer = 0; layer < layers.size(); ++layer) {
        final var source = layers.get(layer);

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

        imageInfos.add(chain.imageInfo());
        chainsForLayers.put(Integer.valueOf(layer), chain);
      }

      checkImageInfos(imageInfos);

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

      writeImageInfo(
        chainsForLayers.get(Integer.valueOf(0)),
        layers.size(),
        writable,
        superCompression
      );
      writeMetadata(writable, metadataFile);
      writeImageArray(compressors, chainsForLayers, writable, superCompression);
      writeEnd(writable);
    }

    return QCommandStatus.SUCCESS;
  }

  private static void checkImageInfos(
    final Set<CLNImageInfo> imageInfos)
  {
    if (imageInfos.size() > 1) {
      LOG.error("the format and size of all source images must be the same");
      throw new IllegalArgumentException(
        "the format and size of all source images must be the same");
    }
  }

  private static void writeMetadata(
    final CLNFileWritableType writable,
    final Optional<Path> metadataFile)
    throws IOException
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

  private static void writeImageArray(
    final CLNCompressors compressors,
    final SortedMap<Integer, CLNImageMipMapChainType> chains,
    final CLNFileWritableType writable,
    final CLNSuperCompressionMethodType superCompression)
    throws IOException
  {
    try (var section = writable.createSectionImageArray()) {
      final var chain0 =
        chains.get(Integer.valueOf(0));
      final var chainSize =
        chain0.mipMapLevelCount();
      final var dataForDescriptions =
        new HashMap<CLNImageArrayMipMapDeclaration, byte[]>();

      /*
       * Create declarations for each layer of each level.
       */

      for (var level = chainSize - 1; level >= 0; --level) {
        for (final var chainEntry : chains.entrySet()) {
          final var layer =
            chainEntry.getKey().intValue();
          final var chain =
            chainEntry.getValue();
          final var data =
            chain.mipMapUncompressedBytes(level);

          /*
           * If the data is uncompressed, then add the data to the list
           * directly.
           */

          if (Objects.equals(superCompression, UNCOMPRESSED)) {
            final var crc32 = new CRC32();
            crc32.update(data);

            final var declaration =
              new CLNImageArrayMipMapDeclaration(
                level,
                layer,
                toUnsignedLong(data.length),
                toUnsignedLong(data.length),
                (int) (crc32.getValue() & 0xffff_ffffL)
              );

            dataForDescriptions.put(declaration, data);
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

          final var compressedData = compressor.execute(data);
          final var crc32 = new CRC32();
          crc32.update(data);

          final var declaration =
            new CLNImageArrayMipMapDeclaration(
              level,
              layer,
              toUnsignedLong(compressedData.length),
              toUnsignedLong(data.length),
              (int) (crc32.getValue() & 0xffff_ffffL)
            );

          dataForDescriptions.put(declaration, compressedData);
        }
      }

      /*
       * For each declaration, write the data for each level and layer.
       */

      final var declarations =
        new CLNImageArrayMipMapDeclarations(
          dataForDescriptions.keySet()
            .stream()
            .sorted()
            .toList(),
          chain0.imageInfo()
            .texelBlockAlignment()
        );

      final var writableMipMaps =
        section.createMipMaps(declarations);

      for (final var declaration : declarations.mipMaps()) {
        final var data = dataForDescriptions.get(declaration);
        final var level = declaration.mipMapLevel();
        final var layer = declaration.layer();
        try (var mipChannel =
               writableMipMaps.writeMipMap(level, layer)) {
          final var wrote = mipChannel.write(ByteBuffer.wrap(data));
          if (wrote != data.length) {
            throw new IOException(
              "Expected to write %d bytes but wrote %d"
                .formatted(
                  Integer.valueOf(data.length),
                  Integer.valueOf(wrote)
                )
            );
          }
        }
      }
    }
  }

  private static void writeEnd(
    final CLNFileWritableType writable)
    throws IOException
  {
    try (var ignored = writable.createSectionEnd()) {
      // Nothing required
    }
  }

  private static void writeImageInfo(
    final CLNImageMipMapChainType chain,
    final int layerCount,
    final CLNFileWritableType writable,
    final CLNSuperCompressionMethodType superCompression)
    throws IOException
  {
    try (var section = writable.createSectionImageInfo()) {
      final var imageInfo = chain.imageInfo();
      final var withCompression = new CLNImageInfo(
        imageInfo.sizeX(),
        imageInfo.sizeY(),
        layerCount,
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
