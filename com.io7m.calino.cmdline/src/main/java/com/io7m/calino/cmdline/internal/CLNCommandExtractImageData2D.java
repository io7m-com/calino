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

import com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.imageview.CLNImageViews;
import com.io7m.jaffirm.core.Invariants;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.quarrel.core.QStringType.QLocalize;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.imageio.ImageIO;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.io.InputStream;
import java.nio.channels.Channels;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

import static com.io7m.calino.api.CLNImageFlagStandard.ALPHA_PREMULTIPLIED;
import static java.awt.image.BufferedImage.TYPE_3BYTE_BGR;
import static java.awt.image.BufferedImage.TYPE_4BYTE_ABGR;
import static java.awt.image.BufferedImage.TYPE_4BYTE_ABGR_PRE;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

/**
 * The 'extract-image-data-2d' command.
 */

public final class CLNCommandExtractImageData2D extends
  CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandExtractImageData2D.class);

  private static final QParameterNamed1<Path> OUTPUT_DIRECTORY =
    new QParameterNamed1<>(
      "--output-directory",
      List.of(),
      new QConstant("The output directory."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed1<Boolean> DECOMPRESS =
    new QParameterNamed1<>(
      "--decompress",
      List.of(),
      new QConstant(
        "Whether to decompress data during extraction (ignored if the output is PNG)."),
      Optional.of(Boolean.TRUE),
      Boolean.class
    );

  private static final QParameterNamed1<CLNOutputFormat> OUTPUT_FORMAT =
    new QParameterNamed1<>(
      "--output-format",
      List.of(),
      new QConstant("The output format."),
      Optional.of(CLNOutputFormat.RAW),
      CLNOutputFormat.class
    );

  /**
   * The 'extract-image-data-2d' command.
   */

  public CLNCommandExtractImageData2D()
  {
    super(
      new QCommandMetadata(
        "extract-image-data-2d",
        new QConstant("Extract 2D image data from a file."),
        Optional.of(new QLocalize("cmd.extract-image-data-2d.helpExt"))
      )
    );
  }

  private static BufferedImage suitablePNGImageFor(
    final CLNImageInfo imageInfo,
    final CLNImage2DDescription imageDescription)
  {
    final var width =
      imageInfo.sizeX() >> imageDescription.mipMapLevel();
    final var height =
      imageInfo.sizeY() >> imageDescription.mipMapLevel();

    final var channelsLayout = imageInfo.channelsLayout();
    if (channelsLayout instanceof final CLNChannelsLayoutDescriptionStandard standard) {
      return switch (standard) {
        case R5_G6_B5,
             R64_G64_B64,
             R64_G64,
             R64,
             R32_G32_B32,
             R32_G32,
             R32,
             R16_G16_B16,
             R16_G16,
             R16,
             R8_G8_B8,
             R8_G8, R8 -> {
          yield new BufferedImage(width, height, TYPE_3BYTE_BGR);
        }
        case A1_R5_G5_B5,
             R4_G4_B4_A4,
             R64_G64_B64_A64,
             R32_G32_B32_A32,
             R16_G16_B16_A16,
             R8_G8_B8_A8 -> {
          final var imageType =
            imageInfo.flags().contains(ALPHA_PREMULTIPLIED)
              ? TYPE_4BYTE_ABGR_PRE
              : TYPE_4BYTE_ABGR;
          yield new BufferedImage(width, height, imageType);
        }
      };
    }

    throw new UnsupportedOperationException(
      new StringBuilder(64)
        .append("Unable to determine a suitable PNG format for channel layout ")
        .append(channelsLayout.descriptor())
        .toString()
    );
  }

  private static void outputPNG(
    final CLNImageInfo imageInfo,
    final CLNSectionReadableImage2DType section2d,
    final CLNImage2DDescription imageDescription,
    final Path outputDirectory)
    throws IOException
  {
    final var outputFile =
      outputDirectory.resolve(
        String.format(
          "m%03d.png",
          Integer.valueOf(imageDescription.mipMapLevel()))
      );

    LOG.info(
      "writing level {} to {}",
      Integer.valueOf(imageDescription.mipMapLevel()),
      outputFile
    );

    final var imageViews = new CLNImageViews();

    try (var inputStream = Channels.newInputStream(
      section2d.mipMapDataWithoutSupercompression(imageDescription))) {
      final var data =
        inputStream.readAllBytes();
      final var view =
        imageViews.createImageView2D(imageInfo, imageDescription, data);

      final var outputImage =
        suitablePNGImageFor(imageInfo, imageDescription);
      final var raster =
        outputImage.getRaster();

      Invariants.checkInvariantV(
        view.sizeX() == raster.getWidth(),
        "View size X %d must match raster size X %d",
        Integer.valueOf(view.sizeX()),
        Integer.valueOf(raster.getWidth())
      );
      Invariants.checkInvariantV(
        view.sizeY() == raster.getHeight(),
        "View size Y %d must match raster size Y %d",
        Integer.valueOf(view.sizeY()),
        Integer.valueOf(raster.getHeight())
      );

      final var pixel = new double[4];
      for (int y = 0; y < view.sizeY(); ++y) {
        for (int x = 0; x < view.sizeX(); ++x) {
          pixel[0] = 0.0;
          pixel[1] = 0.0;
          pixel[2] = 0.0;
          pixel[3] = 1.0;
          view.pixelAt(x, y, pixel);

          pixel[0] *= 255.0;
          pixel[1] *= 255.0;
          pixel[2] *= 255.0;
          pixel[3] *= 255.0;
          raster.setPixel(x, y, pixel);
        }
      }

      ImageIO.write(outputImage, "PNG", outputFile.toFile());
    }
  }

  private static void outputRaw(
    final CLNSectionReadableImage2DType section2d,
    final CLNImage2DDescription imageDescription,
    final Path outputDirectory,
    final boolean decompress)
    throws IOException
  {
    final var outputFile =
      outputDirectory.resolve(
        String.format(
          "m%03d.raw",
          Integer.valueOf(imageDescription.mipMapLevel()))
      );

    LOG.info(
      "Writing level {} to {}",
      Integer.valueOf(imageDescription.mipMapLevel()),
      outputFile
    );

    try (var outputStream =
           Files.newOutputStream(
             outputFile,
             CREATE,
             WRITE,
             TRUNCATE_EXISTING)) {

      final InputStream inputStream;
      if (decompress) {
        inputStream =
          Channels.newInputStream(
            section2d.mipMapDataWithoutSupercompression(imageDescription));
      } else {
        inputStream =
          Channels.newInputStream(
            section2d.mipMapDataRaw(imageDescription));
      }

      inputStream.transferTo(outputStream);
      outputStream.flush();
    }
  }

  @Override
  protected List<QParameterNamedType<?>> onListNamedParametersWithFile()
  {
    return List.of(
      OUTPUT_DIRECTORY,
      DECOMPRESS,
      OUTPUT_FORMAT
    );
  }

  @Override
  protected QCommandStatus executeWithReadFile(
    final QCommandContextType context,
    final CLNFileReadableType fileParsed)
    throws IOException
  {
    final var outputFormat =
      context.parameterValue(OUTPUT_FORMAT);
    final var outputDirectory =
      context.parameterValue(OUTPUT_DIRECTORY);
    final var decompress =
      context.parameterValue(DECOMPRESS)
        .booleanValue();

    if (outputFormat == CLNOutputFormat.PNG) {
      LOG.warn(
        "Extracting to PNG might be a lossy operation due to possible downsampling!");
    }

    final var section2dOpt =
      fileParsed.openImage2D();
    final var sectionImageInfoOpt =
      fileParsed.openImageInfo();

    if (section2dOpt.isPresent() && sectionImageInfoOpt.isPresent()) {
      final var section2d =
        section2dOpt.get();
      final var imageInfo =
        sectionImageInfoOpt.get().info();
      final var imageDescriptions =
        section2d.mipMapDescriptions();

      Files.createDirectories(outputDirectory);

      for (final var imageDescription : imageDescriptions) {
        switch (outputFormat) {
          case RAW ->
            outputRaw(section2d, imageDescription, outputDirectory, decompress);
          case PNG ->
            outputPNG(imageInfo, section2d, imageDescription, outputDirectory);
        }
      }

      return QCommandStatus.SUCCESS;
    }

    LOG.error("No available image 2D section");
    return QCommandStatus.FAILURE;
  }
}
