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

package com.io7m.calino.imageproc.awt.internal;

import com.io7m.calino.api.CLNByteOrder;
import com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard;
import com.io7m.calino.api.CLNChannelsLayoutDescriptionType;
import com.io7m.calino.api.CLNChannelsTypeDescriptionType;
import com.io7m.calino.api.CLNColorSpaceStandard;
import com.io7m.calino.api.CLNColorSpaceType;
import com.io7m.calino.api.CLNCompressionMethodStandard;
import com.io7m.calino.api.CLNCoordinateSystem;
import com.io7m.calino.api.CLNImageFlagType;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.imageproc.api.CLNImageLayoutConversion;
import com.io7m.calino.imageproc.api.CLNImageMipMapChainType;
import com.io7m.calino.imageproc.api.CLNImageMipMapFilter;
import com.io7m.calino.imageproc.api.CLNImageProcessorRequest;
import com.io7m.calino.imageproc.api.CLNImageProcessorType;

import javax.imageio.ImageIO;
import java.awt.color.ColorSpace;
import java.awt.geom.AffineTransform;
import java.awt.image.AffineTransformOp;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.nio.ByteOrder;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R16;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R16_G16_B16;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R16_G16_B16_A16;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R5_G6_B5;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8;
import static com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard.R8_G8_B8_A8;
import static com.io7m.calino.api.CLNChannelsTypeDescriptionStandard.FIXED_POINT_NORMALIZED_UNSIGNED;
import static com.io7m.calino.api.CLNCoordinateAxisR.AXIS_R_INCREASING_TOWARD;
import static com.io7m.calino.api.CLNCoordinateAxisS.AXIS_S_INCREASING_RIGHT;
import static com.io7m.calino.api.CLNCoordinateAxisT.AXIS_T_INCREASING_DOWN;
import static com.io7m.calino.api.CLNImageFlagStandard.ALPHA_PREMULTIPLIED;
import static com.io7m.calino.api.CLNSuperCompressionMethodStandard.UNCOMPRESSED;
import static java.awt.color.ColorSpace.CS_GRAY;
import static java.awt.color.ColorSpace.CS_LINEAR_RGB;
import static java.awt.color.ColorSpace.CS_sRGB;
import static java.awt.image.AffineTransformOp.TYPE_BICUBIC;
import static java.awt.image.AffineTransformOp.TYPE_BILINEAR;
import static java.awt.image.AffineTransformOp.TYPE_NEAREST_NEIGHBOR;

public final class CLNImageProcessor implements CLNImageProcessorType
{
  private static final int[] R5G6B5_SIZES = {5, 6, 5};
  private static final int[] R8G8B8A8_SIZES = {8, 8, 8, 8};
  private static final int[] R8G8B8_SIZES = {8, 8, 8};
  private static final int[] R8_SIZES = {8};
  private static final int[] R16_SIZES = {16};
  private static final int[] R16G16B16A16_SIZES = {16, 16, 16, 16};
  private static final int[] R16G16B16_SIZES = {16, 16, 16};

  private final CLNImageProcessorRequest request;

  public CLNImageProcessor(
    final CLNImageProcessorRequest inRequest)
  {
    this.request =
      Objects.requireNonNull(inRequest, "request");
  }

  private static CLNImageDecodeType createDecoderForLayout(
    final CLNByteOrder byteOrder,
    final CLNChannelsLayoutDescriptionStandard layout)
  {
    final var bufferOrder = switch (byteOrder) {
      case BIG_ENDIAN -> ByteOrder.BIG_ENDIAN;
      case LITTLE_ENDIAN -> ByteOrder.LITTLE_ENDIAN;
    };

    return switch (layout) {
      case R5_G6_B5 -> new CLNImageDecodeR5G6B5();
      case R4_G4_B4_A4 -> new CLNImageDecodeR4G4B4A4();
      case R8 -> new CLNImageDecode8(bufferOrder, 1);
      case R8_G8 -> new CLNImageDecode8(bufferOrder, 2);
      case R8_G8_B8 -> new CLNImageDecode8(bufferOrder, 3);
      case R8_G8_B8_A8 -> new CLNImageDecode8(bufferOrder, 4);
      case R16 -> new CLNImageDecode16(bufferOrder, 1);
      case R16_G16 -> new CLNImageDecode16(bufferOrder, 2);
      case R16_G16_B16 -> new CLNImageDecode16(bufferOrder, 3);
      case R16_G16_B16_A16 -> new CLNImageDecode16(bufferOrder, 4);
      case R32 -> new CLNImageDecode32(bufferOrder, 1);
      case R32_G32 -> new CLNImageDecode32(bufferOrder, 2);
      case R32_G32_B32 -> new CLNImageDecode32(bufferOrder, 3);
      case R32_G32_B32_A32 -> new CLNImageDecode32(bufferOrder, 4);
      case R64 -> new CLNImageDecode64(bufferOrder, 1);
      case R64_G64 -> new CLNImageDecode64(bufferOrder, 2);
      case R64_G64_B64 -> new CLNImageDecode64(bufferOrder, 3);
      case R64_G64_B64_A64 -> new CLNImageDecode64(bufferOrder, 4);
    };
  }

  private static CLNChannelsLayoutDescriptionType channelLayoutGuess(
    final BufferedImage image)
  {
    final var componentBits =
      image.getColorModel().getComponentSize();

    if (Arrays.equals(componentBits, R5G6B5_SIZES)) {
      return R5_G6_B5;
    }
    if (Arrays.equals(componentBits, R8_SIZES)) {
      return R8;
    }
    if (Arrays.equals(componentBits, R16_SIZES)) {
      return R16;
    }
    if (Arrays.equals(componentBits, R8G8B8A8_SIZES)) {
      return R8_G8_B8_A8;
    }
    if (Arrays.equals(componentBits, R8G8B8_SIZES)) {
      return R8_G8_B8;
    }
    if (Arrays.equals(componentBits, R16G16B16A16_SIZES)) {
      return R16_G16_B16_A16;
    }
    if (Arrays.equals(componentBits, R16G16B16_SIZES)) {
      return R16_G16_B16;
    }

    throw new UnsupportedOperationException(
      "Unsupported image type: " + image.getType());
  }

  private static BufferedImage premultiplyAlpha(
    final BufferedImage image)
  {
    image.getColorModel()
      .coerceData(image.getRaster(), true);
    return image;
  }

  private static Set<CLNImageFlagType> flagsOf(
    final BufferedImage image)
  {
    final var flags = new HashSet<CLNImageFlagType>();
    if (image.isAlphaPremultiplied()) {
      flags.add(ALPHA_PREMULTIPLIED);
    }
    return Set.copyOf(flags);
  }

  private static CLNColorSpaceType colorSpaceOf(
    final BufferedImage image)
  {
    final var colorSpace = image.getColorModel().getColorSpace();

    final var linear = ColorSpace.getInstance(CS_LINEAR_RGB);
    if (Objects.equals(colorSpace, linear)) {
      return CLNColorSpaceStandard.COLOR_SPACE_LINEAR;
    }

    final var sRGB = ColorSpace.getInstance(CS_sRGB);
    if (Objects.equals(colorSpace, sRGB)) {
      return CLNColorSpaceStandard.COLOR_SPACE_SRGB;
    }

    /*
     * We assume greyscale images are linear.
     */

    final var grey = ColorSpace.getInstance(CS_GRAY);
    if (Objects.equals(colorSpace, grey)) {
      return CLNColorSpaceStandard.COLOR_SPACE_LINEAR;
    }

    throw new IllegalArgumentException(
      String.format("Unrecognized color space: %s", colorSpace));
  }

  private static CLNChannelsTypeDescriptionType channelTypeOf(
    final BufferedImage image)
  {
    return FIXED_POINT_NORMALIZED_UNSIGNED;
  }

  private static CLNImageMipMapChainType generateMipMapChain(
    final BufferedImage baseImage,
    final CLNByteOrder byteOrder,
    final CLNChannelsLayoutDescriptionType targetLayout,
    final CLNImageMipMapFilter imageMipMapFilter)
  {
    var imageCurrent = baseImage;
    final var images = new ArrayList<BufferedImage>();

    while (true) {
      images.add(imageCurrent);

      final var newWidth = imageCurrent.getWidth() >> 1;
      final var newHeight = imageCurrent.getHeight() >> 1;
      if (newHeight < 2 || newWidth < 2) {
        break;
      }

      final var imageNext =
        new BufferedImage(newWidth, newHeight, imageCurrent.getType());

      final var transform = new AffineTransform();
      transform.scale(0.5, 0.5);

      final var scaleOp =
        new AffineTransformOp(transform, scaling(imageMipMapFilter));
      scaleOp.filter(imageCurrent, imageNext);
      imageCurrent = imageNext;
    }

    final var imageInfo =
      new CLNImageInfo(
        baseImage.getWidth(),
        baseImage.getHeight(),
        1,
        targetLayout,
        channelTypeOf(baseImage),
        CLNCompressionMethodStandard.UNCOMPRESSED,
        UNCOMPRESSED,
        new CLNCoordinateSystem(
          AXIS_R_INCREASING_TOWARD,
          AXIS_S_INCREASING_RIGHT,
          AXIS_T_INCREASING_DOWN
        ),
        colorSpaceOf(baseImage),
        flagsOf(baseImage),
        byteOrder
      );

    return new Chain(imageInfo, images);
  }

  private static int scaling(
    final CLNImageMipMapFilter filter)
  {
    return switch (filter) {
      case NEAREST -> TYPE_NEAREST_NEIGHBOR;
      case BICUBIC -> TYPE_BICUBIC;
      case BILINEAR -> TYPE_BILINEAR;
    };
  }

  @Override
  public CLNImageMipMapChainType process()
    throws IOException
  {
    final var baseImage =
      ImageIO.read(this.request.file().toFile());

    final var image =
      this.premultiplyAlphaIfRequested(baseImage);

    final var finalLayout =
      this.request.layoutConversion()
        .map(CLNImageLayoutConversion::targetLayout)
        .orElse(channelLayoutGuess(image));

    /*
     * If mipmap generation is requested, then generate mipmaps.
     */

    if (this.request.generateMipMaps().isPresent()) {
      return generateMipMapChain(
        image,
        this.request.targetByteOrder(),
        finalLayout,
        this.request.generateMipMaps().get()
      );
    }

    final var imageInfo =
      new CLNImageInfo(
        image.getWidth(),
        image.getHeight(),
        1,
        finalLayout,
        channelTypeOf(image),
        CLNCompressionMethodStandard.UNCOMPRESSED,
        UNCOMPRESSED,
        new CLNCoordinateSystem(
          AXIS_R_INCREASING_TOWARD,
          AXIS_S_INCREASING_RIGHT,
          AXIS_T_INCREASING_DOWN
        ),
        colorSpaceOf(image),
        flagsOf(image),
        this.request.targetByteOrder()
      );

    return new Chain(imageInfo, List.of(image));
  }

  /**
   * If alpha premultiplication is requested, and the image has alpha and isn't
   * premultiplied... Premultiply!
   */

  private BufferedImage premultiplyAlphaIfRequested(
    final BufferedImage image)
  {
    if (this.request.premultiplyAlpha()) {
      final var hasAlpha =
        image.getColorModel().hasAlpha();
      final var isPremultiplied =
        image.isAlphaPremultiplied();

      if (hasAlpha && !isPremultiplied) {
        return premultiplyAlpha(image);
      }
    }
    return image;
  }

  private static final class Chain implements CLNImageMipMapChainType
  {
    private final List<BufferedImage> images;
    private final CLNImageInfo imageInfo;
    private final List<byte[]> uncompressedBytes;

    Chain(
      final CLNImageInfo inImageInfo,
      final List<BufferedImage> inImages)
    {
      this.imageInfo =
        Objects.requireNonNull(inImageInfo, "imageInfo");
      this.images = List.copyOf(
        Objects.requireNonNull(inImages, "images")
      );

      this.uncompressedBytes =
        this.images.stream()
          .map(this::extractBytes)
          .collect(Collectors.toList());
    }

    private byte[] extractBytes(
      final BufferedImage image)
    {
      final var layout = this.imageInfo.channelsLayout();
      if (layout instanceof CLNChannelsLayoutDescriptionStandard standard) {
        final var decoder =
          createDecoderForLayout(this.imageInfo.dataByteOrder(), standard);
        return decoder.execute(image);
      }

      throw new IllegalStateException();
    }

    @Override
    public CLNImageInfo imageInfo()
    {
      return this.imageInfo;
    }

    @Override
    public int mipMapLevelCount()
    {
      return this.images.size();
    }

    @Override
    public byte[] mipMapUncompressedBytes(
      final int level)
    {
      if (level < this.images.size()) {
        return this.uncompressedBytes.get(level);
      }

      throw new IllegalArgumentException(
        String.format(
          "No such mipmap level (valid range is [0, %d])",
          Integer.valueOf(this.images.size() - 1))
      );
    }
  }
}
