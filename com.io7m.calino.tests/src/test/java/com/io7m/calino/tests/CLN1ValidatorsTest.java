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

import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParserValidationEvent;
import com.io7m.calino.parser.api.CLNParsers;
import com.io7m.calino.supercompression.api.CLNDecompressors;
import com.io7m.calino.validation.api.CLNValidationError;
import com.io7m.calino.validation.api.CLNValidationRequest;
import com.io7m.calino.validation.api.CLNValidatorType;
import com.io7m.calino.vanilla.CLN1Validators;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.URI;
import java.nio.channels.FileChannel;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static java.nio.file.StandardOpenOption.READ;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class CLN1ValidatorsTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN1ValidatorsTest.class);

  private Path directory;
  private Path directoryOutput;
  private CLNParsers parsers;
  private ArrayList<CLNParserValidationEvent> validationEvents;
  private FileChannel channel;
  private CLN1Validators validators = new CLN1Validators();

  private CLNValidatorType validatorFor(
    final CLNFileReadableType file,
    final URI source)
  {
    return this.validators.createValidator(
      new CLNValidationRequest(file, source)
    );
  }

  @BeforeEach
  public void setup()
    throws IOException
  {
    this.parsers =
      new CLNParsers();
    this.directory =
      CLNTestDirectories.createTempDirectory();
    this.validationEvents =
      new ArrayList<CLNParserValidationEvent>();
  }

  @AfterEach
  public void tearDown()
    throws IOException
  {
    this.channel.close();
    CLNTestDirectories.deleteDirectory(this.directory);
  }

  /**
   * An empty file cannot validate.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationEmpty()
    throws Exception
  {
    final var errors =
      this.validate("validation-empty.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "The first section in a texture should be an image information section.",
      errors.remove(0).message()
    );
  }

  /**
   * A 2D image with an incorrect Z size fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidation2DWrongZ()
    throws Exception
  {
    final var errors =
      this.validate("validation-2d-wrong-size-z.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "The Z size of a 2D image must equal 1, but was 23.",
      errors.remove(0).message()
    );
  }

  /**
   * A 2D image with a duplicate mipmap fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidation2DMipMapDuplicate()
    throws Exception
  {
    final var errors =
      this.validate("validation-2d-mip-duplicate.ctf");

    assertEquals(2, errors.size());
    assertEquals(
      "Duplicate mip level 2 specified.",
      errors.remove(0).message()
    );
    assertEquals(
      "Mip levels must be strictly decreasing with all values present in the range [0 … 2].",
      errors.remove(0).message()
    );
  }

  /**
   * A 2D image with a disordered mipmaps fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidation2DMipMapDisordered()
    throws Exception
  {
    final var errors =
      this.validate("validation-2d-mip-disordered.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "Mip levels must be strictly decreasing with all values present in the range [0 … 2].",
      errors.remove(0).message()
    );
  }

  /**
   * A 2D image with an incorrect uncompressed size fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidation2DIncorrectSize0()
    throws Exception
  {
    final var errors =
      this.validate("validation-2d-lz4-size-wrong-0.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "The mipmap description for level 2 specifies that the mipmap data should be 13 octets uncompressed, but the actual data was 12 octets.",
      errors.remove(0).message()
    );
  }

  /**
   * A 2D image with an incorrect compressed size fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidation2DIncorrectSize1()
    throws Exception
  {
    final var errors =
      this.validate("validation-2d-lz4-size-wrong-1.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "I/O error reading compressed mipmap data: Stream ended prematurely",
      errors.remove(0).message()
    );
  }

  /**
   * A 2D image with an incorrect CRC32 fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidation2DIncorrectCRC32()
    throws Exception
  {
    final var errors =
      this.validate("validation-2d-crc-mismatch.ctf");

    assertEquals(2, errors.size());
    assertEquals(
      "The mipmap description for level 2 specifies a CRC32 value of 0x7bd5d66f but the actual data had a CRC32 of 0x7bd5c66f.",
      errors.remove(0).message()
    );
    assertEquals(
      "The mipmap description for level 0 specifies a CRC32 value of 0x8bef08f2 but the actual data had a CRC32 of 0x8bff08f2.",
      errors.remove(0).message()
    );
  }

  /**
   * An array image with more actual than declared layers, fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationArrayLayersTooFew()
    throws Exception
  {
    final var errors =
      this.validate("validation-array-layers-too-few.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "The texture file specifies a Z size of 10 but provides 3 layers.",
      errors.remove(0).message()
    );
  }

  /**
   * An array image with fewer actual than declared layers, fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationArrayLayersTooMany()
    throws Exception
  {
    final var errors =
      this.validate("validation-array-layers-too-many.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "The texture file specifies a Z size of 2 but provides 3 layers.",
      errors.remove(0).message()
    );
  }

  /**
   * An array image with an incorrect CRC32 fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationArrayIncorrectCRC32()
    throws Exception
  {
    final var errors =
      this.validate("validation-array-crc-mismatch.ctf");

    assertEquals(3, errors.size());
    assertEquals(
      "The mipmap description for layer 0, level 0 specifies a CRC32 value of 0xc51c71a5 but the actual data had a CRC32 of 0xc51b71a5.",
      errors.remove(0).message()
    );
    assertEquals(
      "The mipmap description for layer 1, level 0 specifies a CRC32 value of 0x6b150b10 but the actual data had a CRC32 of 0x6b050b10.",
      errors.remove(0).message()
    );
    assertEquals(
      "The mipmap description for layer 2, level 0 specifies a CRC32 value of 0xb415f4f8 but the actual data had a CRC32 of 0xa415f4f8.",
      errors.remove(0).message()
    );
  }

  /**
   * An array image with an incorrect compressed size fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationArrayIncorrectSize0()
    throws Exception
  {
    final var errors =
      this.validate("validation-array-lz4-size-wrong-0.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "I/O error reading compressed mipmap data: Stream ended prematurely",
      errors.remove(0).message()
    );
  }

  /**
   * An array image with an incorrect uncompressed size fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationArrayIncorrectSize1()
    throws Exception
  {
    final var errors =
      this.validate("validation-array-lz4-size-wrong-1.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "The mipmap description for layer 0, level 0 specifies that the mipmap data should be 193 octets uncompressed, but the actual data was 192 octets.",
      errors.remove(0).message()
    );
  }

  /**
   * An array image with non-unique layers/levels fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationArrayMipNotUnique0()
    throws Exception
  {
    final var errors =
      this.validate("validation-array-not-unique-0.ctf");

    assertEquals(2, errors.size());
    assertEquals(
      "Mip layer 0, layer 0 is not unique.",
      errors.remove(0).message()
    );
    assertEquals(
      "Mip layers (for level 0) must be strictly increasing with all values present in the range [0 … 2] (received {0, 2}).",
      errors.remove(0).message()
    );
  }

  /**
   * An array image with non-unique layers/levels fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationArrayMipNotUnique1()
    throws Exception
  {
    final var errors =
      this.validate("validation-array-not-unique-1.ctf");

    assertEquals(2, errors.size());
    assertEquals(
      "Mip layer 1, layer 2 is not unique.",
      errors.remove(0).message()
    );
    assertEquals(
      "Mip layers (for level 2) must be strictly increasing with all values present in the range [0 … 2] (received {0, 1}).",
      errors.remove(0).message()
    );
  }

  /**
   * An array image with disordered layers fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationArrayDisordered0()
    throws Exception
  {
    final var errors =
      this.validate("validation-array-disordered-0.ctf");

    assertEquals(1, errors.size());
    assertEquals(
      "Mip levels must be strictly decreasing with all values present in the range [0 … 2].",
      errors.remove(0).message()
    );
  }

  /**
   * An array image with disordered layers fails.
   *
   * @throws Exception On errors
   */

  @Test
  public void testValidationArrayLevelOutOfRange0()
    throws Exception
  {
    final var errors =
      this.validate("validation-array-level-out-of-range-0.ctf");

    assertEquals(4, errors.size());
    assertEquals(
      "Mip layers (for level 0) must be strictly increasing with all values present in the range [0 … 2] (received {0, 2}).",
      errors.remove(0).message()
    );
    assertEquals(
      "Mip layers (for level 1) must be strictly increasing with all values present in the range [0 … 2] (received {1}).",
      errors.remove(0).message()
    );
    assertEquals(
      "Mip layers (for level 1) must be strictly increasing with all values present in the range [0 … 2] (received {1}).",
      errors.remove(0).message()
    );
    assertEquals(
      "Mip levels must be strictly decreasing with all values present in the range [0 … 1].",
      errors.remove(0).message()
    );
  }

  private List<CLNValidationError> validate(
    final String name)
    throws IOException
  {
    final var file = this.fileOf(name);
    return this.validatorFor(file, URI.create("urn:source")).execute();
  }

  private CLNFileReadableType fileOf(
    final String name)
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ValidatorsTest.class, this.directory, name);

    this.channel = FileChannel.open(file, READ);

    final var request =
      new CLNParseRequest(
        new CLNDecompressors(),
        this.channel,
        file.toUri(),
        this::onParserValidationEvent,
        8192L,
        8192L
      );
    try (var parser = this.parsers.createParser(request)) {
      return parser.execute();
    }
  }

  private boolean onParserValidationEvent(
    final CLNParserValidationEvent event)
  {
    LOG.debug("{}", event);
    return this.validationEvents.add(event);
  }
}
