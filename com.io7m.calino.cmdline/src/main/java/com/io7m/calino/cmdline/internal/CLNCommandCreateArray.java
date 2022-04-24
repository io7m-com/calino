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

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
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
import com.io7m.claypot.core.CLPCommandContextType;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.ClosingResourceFailedException;
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
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Properties;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.zip.CRC32;

import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.UNCOMPRESSED;
import static com.io7m.claypot.core.CLPCommandType.Status.FAILURE;
import static com.io7m.claypot.core.CLPCommandType.Status.SUCCESS;
import static java.lang.Integer.toUnsignedLong;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

/**
 * The 'create-array' command.
 */

@Parameters(commandDescription = "Create an array texture from an existing image.")
public final class CLNCommandCreateArray extends CLNAbstractCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandCreateArray.class);

  @Parameter(
    required = true,
    description = "The source image layer files, in layer order starting at 0",
    names = "--source-layer")
  private List<Path> layers;

  @Parameter(
    required = true,
    description = "The output texture file",
    names = "--output")
  private Path output;

  @Parameter(
    required = false,
    description = "The mipmap filter",
    names = "--mipmap-generate")
  private CLNImageMipMapFilter mipMapGenerate;

  @Parameter(
    required = false,
    description = "Premultiply alpha",
    arity = 1,
    names = "--premultiply-alpha")
  private boolean premultiplyAlpha;

  @Parameter(
    required = false,
    description = "The byte order used for image data",
    names = "--byte-order")
  private CLNByteOrder byteOrder = CLNByteOrder.LITTLE_ENDIAN;

  @Parameter(
    required = false,
    description = "The requested file format version",
    converter = CLNVersionStringConverter.class,
    names = "--format-version")
  private CLNVersion formatVersion = new CLNVersion(1, 0);

  @Parameter(
    required = false,
    converter = CLNChannelLayoutStringConverter.class,
    description = "The requested layout to which to convert",
    names = "--convert-layout-to")
  private CLNChannelsLayoutDescriptionType convertLayoutTo;

  @Parameter(
    required = false,
    converter = CLNSuperCompressionMethodConverter.class,
    description = "The super compression method.",
    names = "--super-compression")
  private CLNSuperCompressionMethodType superCompression = UNCOMPRESSED;

  @Parameter(
    required = false,
    description = "A Java properties file containing metadata for the texture file.",
    names = "--metadata")
  private Path metadataFile;

  /**
   * The 'create-array' command.
   *
   * @param inContext The context
   */

  public CLNCommandCreateArray(
    final CLPCommandContextType inContext)
  {
    super(Locale.getDefault(), inContext);
  }

  @Override
  public String extendedHelp()
  {
    return this.calinoStrings().format("cmd.create-array.helpExt");
  }

  @Override
  protected Status executeActual()
    throws IOException, ClosingResourceFailedException
  {
    final var writers = new CLNWriters();

    final var writerOpt =
      writers.findWriterFactoryFor(this.formatVersion);

    if (writerOpt.isEmpty()) {
      LOG.error(
        "no available writers for format version {}",
        this.formatVersion);
      return FAILURE;
    }

    if (this.layers.isEmpty()) {
      LOG.error("at least one image source file is required");
      return FAILURE;
    }

    final var writerFactory = writerOpt.get();
    final var processors = new CLNImageProcessorsAWT();
    final var compressors = new CLNCompressors();

    try (var resources = CloseableCollection.create()) {
      final var imageInfos =
        new HashSet<CLNImageInfo>();
      final var chainsForLayers =
        new TreeMap<Integer, CLNImageMipMapChainType>();

      for (int layer = 0; layer < this.layers.size(); ++layer) {
        final var source = this.layers.get(layer);

        final var layoutConversion =
          Optional.ofNullable(this.convertLayoutTo)
            .map(CLNImageLayoutConversion::new);

        final var processorRequest =
          new CLNImageProcessorRequest(
            source,
            this.premultiplyAlpha,
            this.byteOrder,
            layoutConversion,
            Optional.ofNullable(this.mipMapGenerate)
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
          FileChannel.open(this.output, CREATE, WRITE, TRUNCATE_EXISTING)
        );

      final var request =
        new CLNWriteRequest(channel, this.output.toUri(), this.formatVersion);
      final var writer =
        resources.add(writerFactory.createWriter(request));
      final var writable =
        resources.add(writer.execute());

      this.writeImageInfo(
        chainsForLayers.get(Integer.valueOf(0)),
        this.layers.size(),
        writable
      );
      this.writeMetadata(writable);
      this.writeImageArray(compressors, chainsForLayers, writable);
      this.writeEnd(writable);
    }

    return SUCCESS;
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

  private void writeMetadata(
    final CLNFileWritableType writable)
    throws IOException
  {
    if (this.metadataFile != null) {
      final var data = this.openMetadataFile();
      try (var section = writable.createSectionMetadata()) {
        section.setMetadata(data);
      }
    }
  }

  private Map<String, List<String>> openMetadataFile()
    throws IOException
  {
    try (var stream = Files.newInputStream(this.metadataFile)) {
      final var properties = new Properties();
      properties.load(stream);
      final var data = new HashMap<String, List<String>>(properties.size());
      for (final var entry : properties.entrySet()) {
        data.put((String) entry.getKey(), List.of((String) entry.getValue()));
      }
      return data;
    }
  }

  private void writeImageArray(
    final CLNCompressors compressors,
    final SortedMap<Integer, CLNImageMipMapChainType> chains,
    final CLNFileWritableType writable)
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

          if (Objects.equals(this.superCompression, UNCOMPRESSED)) {
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
              new CLNCompressorRequest(this.superCompression)
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

  private void writeEnd(
    final CLNFileWritableType writable)
    throws IOException
  {
    try (var ignored = writable.createSectionEnd()) {
      // Nothing required
    }
  }

  private void writeImageInfo(
    final CLNImageMipMapChainType chain,
    final int layerCount,
    final CLNFileWritableType writable)
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
        this.superCompression,
        imageInfo.coordinateSystem(),
        imageInfo.colorSpace(),
        imageInfo.flags(),
        imageInfo.dataByteOrder()
      );
      section.setImageInfo(withCompression);
    }
  }

  @Override
  public String name()
  {
    return "create-array";
  }
}
