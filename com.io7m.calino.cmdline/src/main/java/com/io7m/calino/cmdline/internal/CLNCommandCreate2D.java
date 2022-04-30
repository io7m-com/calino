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
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Properties;
import java.util.zip.CRC32;

import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.UNCOMPRESSED;
import static com.io7m.claypot.core.CLPCommandType.Status.FAILURE;
import static com.io7m.claypot.core.CLPCommandType.Status.SUCCESS;
import static java.lang.Integer.toUnsignedLong;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

/**
 * The 'create-2d' command.
 */

@Parameters(commandDescription = "Create a 2D texture from an existing image.")
public final class CLNCommandCreate2D extends CLNAbstractCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandCreate2D.class);

  @Parameter(
    required = true,
    description = "The source image file",
    names = "--source")
  private Path source;

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
   * The 'create-2d' command.
   *
   * @param inContext The context
   */

  public CLNCommandCreate2D(
    final CLPCommandContextType inContext)
  {
    super(Locale.getDefault(), inContext);
  }

  @Override
  public String extendedHelp()
  {
    return this.calinoStrings().format("cmd.create2d.helpExt");
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

    final var writerFactory = writerOpt.get();
    final var processors = new CLNImageProcessorsAWT();
    final var compressors = new CLNCompressors();

    try (var resources = CloseableCollection.create()) {
      final var layoutConversion =
        Optional.ofNullable(this.convertLayoutTo)
          .map(CLNImageLayoutConversion::new);

      final var processorRequest =
        new CLNImageProcessorRequest(
          this.source,
          this.premultiplyAlpha,
          this.byteOrder,
          layoutConversion,
          Optional.ofNullable(this.mipMapGenerate)
        );

      final var processor =
        processors.createProcessor(processorRequest);
      final var chain =
        processor.process();

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

      this.writeImageInfo(chain, writable);
      this.writeMetadata(writable);
      this.writeImage2D(compressors, chain, writable);
      this.writeEnd(writable);
    }

    return SUCCESS;
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

  private void writeImage2D(
    final CLNCompressors compressors,
    final CLNImageMipMapChainType chain,
    final CLNFileWritableType writable)
    throws IOException
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

        if (Objects.equals(this.superCompression, UNCOMPRESSED)) {
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
            new CLNCompressorRequest(this.superCompression)
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
    final CLNFileWritableType writable)
    throws IOException
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
    return "create-2d";
  }
}
