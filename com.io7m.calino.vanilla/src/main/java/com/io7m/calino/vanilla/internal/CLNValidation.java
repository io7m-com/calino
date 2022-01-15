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

package com.io7m.calino.vanilla.internal;

import com.io7m.calino.parser.api.CLNParserValidationEvent;

import java.net.URI;
import java.util.Objects;
import java.util.UUID;

/**
 * Validation events.
 */

public final class CLNValidation
{
  private static final UUID SECTION_UNALIGNED =
    UUID.fromString("2ccedb5d-d5ec-40ba-a965-04bba40ce4ec");
  private static final UUID SECTION_END_NONZERO_SIZE =
    UUID.fromString("75b25aca-58ce-4dfe-9c1b-c3140fda18e3");
  private static final UUID SECTION_END_TRAILING =
    UUID.fromString("e5108d48-42fd-4de3-8137-f42aafc44e20");
  private static final UUID IMAGE_DATA_MIPMAP_COUNT_ZERO =
    UUID.fromString("7d6373a7-e330-4cec-8528-b054a1c683ef");
  private static final UUID IMAGE_DATA_SIZE_UNCOMPRESSED_ZERO =
    UUID.fromString("41c816ac-d7ee-4041-a764-9a36a983080c");
  private static final UUID IMAGE_DATA_SIZE_COMPRESSED_ZERO =
    UUID.fromString("2c3420bb-1273-4f1e-9212-9f259d60d6f1");
  private static final UUID IMAGE_DATA_OFFSET_WITHIN_SECTION_ZERO =
    UUID.fromString("6dbe0c0e-15bd-4035-9132-7505f4c35173");
  private static final UUID IMAGE_DATA_SIZE_COMPRESSION_MISMATCH =
    UUID.fromString("e676eaef-f25a-44e8-9360-bcfaf35ce1e6");

  private CLNValidation()
  {

  }

  /**
   * A section is unaligned.
   *
   * @param source     The source file
   * @param fileOffset The file offset
   * @param sectionId  The section ID
   *
   * @return An event
   */

  public static CLNParserValidationEvent sectionUnaligned(
    final URI source,
    final long fileOffset,
    final long sectionId)
  {
    Objects.requireNonNull(source, "source");

    return new CLNParserValidationEvent(
      source,
      fileOffset,
      SECTION_UNALIGNED,
      false,
      String.format(
        "Section 0x%s is not aligned to a 16 octet boundary.",
        Long.toUnsignedString(sectionId, 16)
      )
    );
  }

  /**
   * An end section has a non-zero size.
   *
   * @param source     The source file
   * @param fileOffset The file offset
   * @param size       The section size
   *
   * @return An event
   */

  public static CLNParserValidationEvent sectionEndNonzeroSize(
    final URI source,
    final long fileOffset,
    final long size)
  {
    Objects.requireNonNull(source, "source");

    return new CLNParserValidationEvent(
      source,
      fileOffset,
      SECTION_END_NONZERO_SIZE,
      false,
      String.format(
        "The 'end' section is of a non-zero size (%s)",
        Long.toUnsignedString(size)
      )
    );
  }

  /**
   * There is data after the end section.
   *
   * @param source     The source file
   * @param fileOffset The file offset
   * @param trailing   The trailing data size
   *
   * @return An event
   */

  public static CLNParserValidationEvent sectionEndTrailing(
    final URI source,
    final long fileOffset,
    final long trailing)
  {
    Objects.requireNonNull(source, "source");

    return new CLNParserValidationEvent(
      source,
      fileOffset,
      SECTION_END_TRAILING,
      false,
      String.format(
        "%s octets of trailing data after the 'end' section.",
        Long.toUnsignedString(trailing)
      )
    );
  }

  /**
   * An image has zero mipmaps.
   *
   * @param source     The source file
   * @param fileOffset The file offset
   *
   * @return An event
   */

  public static CLNParserValidationEvent imageDataMipMapCountZero(
    final URI source,
    final long fileOffset)
  {
    Objects.requireNonNull(source, "source");

    return new CLNParserValidationEvent(
      source,
      fileOffset,
      IMAGE_DATA_MIPMAP_COUNT_ZERO,
      false,
      "The specified mipmap count should be greater than zero."
    );
  }

  /**
   * An image has a zero uncompressed size.
   *
   * @param source     The source file
   * @param fileOffset The file offset
   *
   * @return An event
   */

  public static CLNParserValidationEvent imageDataSizeUncompressedZero(
    final URI source,
    final long fileOffset)
  {
    Objects.requireNonNull(source, "source");

    return new CLNParserValidationEvent(
      source,
      fileOffset,
      IMAGE_DATA_SIZE_UNCOMPRESSED_ZERO,
      false,
      "The uncompressed data size should be greater than zero."
    );
  }

  /**
   * An image has a zero compressed size.
   *
   * @param source     The source file
   * @param fileOffset The file offset
   *
   * @return An event
   */

  public static CLNParserValidationEvent imageDataSizeCompressedZero(
    final URI source,
    final long fileOffset)
  {
    Objects.requireNonNull(source, "source");

    return new CLNParserValidationEvent(
      source,
      fileOffset,
      IMAGE_DATA_SIZE_COMPRESSED_ZERO,
      false,
      "The compressed data size should be greater than zero."
    );
  }

  /**
   * An image has an invalid offset within a section.
   *
   * @param source     The source file
   * @param fileOffset The file offset
   *
   * @return An event
   */

  public static CLNParserValidationEvent imageDataOffsetWithinSectionZero(
    final URI source,
    final long fileOffset)
  {
    Objects.requireNonNull(source, "source");

    return new CLNParserValidationEvent(
      source,
      fileOffset,
      IMAGE_DATA_OFFSET_WITHIN_SECTION_ZERO,
      false,
      "The data offset within a section should be greater than zero."
    );
  }

  /**
   * An image has compressed/uncompressed size mismatch when not compressed.
   *
   * @param source               The source file
   * @param fileOffset           The file offset
   * @param dataSizeCompressed   The compressed size
   * @param dataSizeUncompressed The uncompressed size
   *
   * @return An event
   */

  public static CLNParserValidationEvent imageDataSizeCompressionSizeMismatch(
    final URI source,
    final long fileOffset,
    final long dataSizeCompressed,
    final long dataSizeUncompressed)
  {
    Objects.requireNonNull(source, "source");

    return new CLNParserValidationEvent(
      source,
      fileOffset,
      IMAGE_DATA_SIZE_COMPRESSION_MISMATCH,
      false,
      String.format(
        "For image data without supercompression, the compressed size (%s) and uncompressed size (%s) should match",
        Long.toUnsignedString(dataSizeCompressed),
        Long.toUnsignedString(dataSizeUncompressed)
      )
    );
  }
}
