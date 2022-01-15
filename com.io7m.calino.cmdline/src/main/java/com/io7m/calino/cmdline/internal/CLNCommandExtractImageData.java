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
import com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImage2DType;
import com.io7m.calino.imageview.CLNImageViews;
import com.io7m.claypot.core.CLPCommandContextType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.imageio.ImageIO;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.io.InputStream;
import java.nio.channels.Channels;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;

import static com.io7m.calino.api.CLNImageFlagStandard.ALPHA_PREMULTIPLIED;
import static com.io7m.claypot.core.CLPCommandType.Status.FAILURE;
import static com.io7m.claypot.core.CLPCommandType.Status.SUCCESS;
import static java.awt.image.BufferedImage.TYPE_3BYTE_BGR;
import static java.awt.image.BufferedImage.TYPE_4BYTE_ABGR;
import static java.awt.image.BufferedImage.TYPE_4BYTE_ABGR_PRE;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

/**
 * The 'extract-image-data' command.
 */

@Parameters(commandDescription = "Extract image data from a file")
public final class CLNCommandExtractImageData extends CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandExtractImageData.class);

  @Parameter(
    required = true,
    description = "The output file",
    names = "--output-file")
  private Path outputFile;

  @Parameter(
    required = false,
    description = "The mipmap level",
    names = "--mipmap-level")
  private int mipMapLevel;

  @Parameter(
    required = false,
    description = "Whether to decompress data during extraction (ignored if the output is PNG).",
    arity = 1,
    names = "--decompress")
  private boolean decompress = true;

  @Parameter(
    required = false,
    description = "The output format",
    names = "--output-format")
  private CLNOutputFormat outputFormat = CLNOutputFormat.RAW;

  /**
   * The 'extract-image-data' command.
   *
   * @param inContext The context
   */

  public CLNCommandExtractImageData(
    final CLPCommandContextType inContext)
  {
    super(inContext);
  }

  @Override
  public String extendedHelp()
  {
    return this.calinoStrings().format("cmd.extract-image-data.helpExt");
  }

  @Override
  protected Status executeWithReadFile(
    final CLNFileReadableType fileParsed)
    throws IOException
  {
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

      for (final var imageDescription : imageDescriptions) {
        if (imageDescription.mipMapLevel() == this.mipMapLevel) {
          return switch (this.outputFormat) {
            case RAW -> this.outputRaw(section2d, imageDescription);
            case PNG -> this.outputPNG(imageInfo, section2d, imageDescription);
          };
        }
      }

      LOG.error(
        "no such mipmap level (valid range is [0, {}}])",
        imageDescriptions.stream()
          .max(Comparator.comparingInt(CLNImage2DDescription::mipMapLevel))
          .get()
          .mipMapLevel()
      );
      return FAILURE;
    }

    LOG.error("no available image 2D section");
    return FAILURE;
  }

  private Status outputPNG(
    final CLNImageInfo imageInfo,
    final CLNSectionReadableImage2DType section2d,
    final CLNImage2DDescription imageDescription)
    throws IOException
  {
    LOG.warn("extracting to PNG is a lossy operation due to downsampling!");

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

      final var pixel = new double[4];
      for (int y = 0; y < imageInfo.sizeY(); ++y) {
        for (int x = 0; x < imageInfo.sizeX(); ++x) {
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

      ImageIO.write(outputImage, "PNG", this.outputFile.toFile());
      return SUCCESS;
    }
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
    if (channelsLayout instanceof CLNChannelsLayoutDescriptionStandard standard) {
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
        case R4_G4_B4_A4,
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

  private Status outputRaw(
    final CLNSectionReadableImage2DType section2d,
    final CLNImage2DDescription imageDescription)
    throws IOException
  {
    try (var outputStream =
           Files.newOutputStream(
             this.outputFile, CREATE, WRITE, TRUNCATE_EXISTING)) {

      final InputStream inputStream;
      if (this.decompress) {
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
      return SUCCESS;
    }
  }

  @Override
  public String name()
  {
    return "extract-image-data";
  }
}
