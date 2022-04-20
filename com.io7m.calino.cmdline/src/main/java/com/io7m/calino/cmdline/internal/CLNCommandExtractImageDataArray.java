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
import com.io7m.calino.api.CLNImageArrayDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImageArrayType;
import com.io7m.calino.imageview.CLNImageViews;
import com.io7m.claypot.core.CLPCommandContextType;
import com.io7m.jaffirm.core.Invariants;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.imageio.ImageIO;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.io.InputStream;
import java.nio.channels.Channels;
import java.nio.file.Files;
import java.nio.file.Path;

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
 * The 'extract-image-data-2d' command.
 */

@Parameters(commandDescription = "Extract array image data from a file")
public final class CLNCommandExtractImageDataArray extends
  CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandExtractImageDataArray.class);

  @Parameter(
    required = true,
    description = "The output directory",
    names = "--output-directory")
  private Path outputDirectory;

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
   * The 'extract-image-data-array' command.
   *
   * @param inContext The context
   */

  public CLNCommandExtractImageDataArray(
    final CLPCommandContextType inContext)
  {
    super(inContext);
  }

  @Override
  public String extendedHelp()
  {
    return this.calinoStrings().format("cmd.extract-image-data-array.helpExt");
  }

  @Override
  protected Status executeWithReadFile(
    final CLNFileReadableType fileParsed)
    throws IOException
  {
    if (this.outputFormat == CLNOutputFormat.PNG) {
      LOG.warn("extracting to PNG might be a lossy operation due to possible downsampling!");
    }

    final var sectionArrayOpt =
      fileParsed.openImageArray();
    final var sectionImageInfoOpt =
      fileParsed.openImageInfo();

    if (sectionArrayOpt.isPresent() && sectionImageInfoOpt.isPresent()) {
      final var sectionArray =
        sectionArrayOpt.get();
      final var imageInfo =
        sectionImageInfoOpt.get().info();
      final var imageDescriptions =
        sectionArray.mipMapDescriptions();

      Files.createDirectories(this.outputDirectory);

      for (final var imageDescription : imageDescriptions) {
        switch (this.outputFormat) {
          case RAW -> this.outputRaw(sectionArray, imageDescription);
          case PNG -> this.outputPNG(imageInfo, sectionArray, imageDescription);
        }
      }

      return SUCCESS;
    }

    LOG.error("no available image 2D section");
    return FAILURE;
  }

  private void outputPNG(
    final CLNImageInfo imageInfo,
    final CLNSectionReadableImageArrayType sectionArray,
    final CLNImageArrayDescription imageDescription)
    throws IOException
  {
    final var outputFile =
      this.outputDirectory.resolve(
        String.format(
          "m%03dv%03d.png",
          Integer.valueOf(imageDescription.mipMapLevel()),
          Integer.valueOf(imageDescription.layer())
        )
      );

    LOG.info(
      "writing level {} layer {} to {}",
      Integer.valueOf(imageDescription.mipMapLevel()),
      Integer.valueOf(imageDescription.layer()),
      outputFile
    );

    final var imageViews = new CLNImageViews();

    try (var inputStream = Channels.newInputStream(
      sectionArray.mipMapDataWithoutSupercompression(imageDescription))) {
      final var data =
        inputStream.readAllBytes();
      final var view =
        imageViews.createImageViewArray(imageInfo, imageDescription, data);

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

  private static BufferedImage suitablePNGImageFor(
    final CLNImageInfo imageInfo,
    final CLNImageArrayDescription imageDescription)
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
        case
          A1_R5_G5_B5,
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

  private void outputRaw(
    final CLNSectionReadableImageArrayType sectionArray,
    final CLNImageArrayDescription imageDescription)
    throws IOException
  {
    final var outputFile =
      this.outputDirectory.resolve(
        String.format(
          "m%03dv%03d.raw",
          Integer.valueOf(imageDescription.mipMapLevel()),
          Integer.valueOf(imageDescription.layer())
        )
      );

    LOG.info(
      "writing level {} layer {} to {}",
      Integer.valueOf(imageDescription.mipMapLevel()),
      Integer.valueOf(imageDescription.layer()),
      outputFile
    );

    try (var outputStream =
           Files.newOutputStream(
             outputFile,
             CREATE,
             WRITE,
             TRUNCATE_EXISTING)) {

      final InputStream inputStream;
      if (this.decompress) {
        inputStream =
          Channels.newInputStream(
            sectionArray.mipMapDataWithoutSupercompression(imageDescription));
      } else {
        inputStream =
          Channels.newInputStream(
            sectionArray.mipMapDataRaw(imageDescription));
      }

      inputStream.transferTo(outputStream);
      outputStream.flush();
    }
  }

  @Override
  public String name()
  {
    return "extract-image-data-array";
  }
}
