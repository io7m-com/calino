/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParsers;
import com.io7m.calino.supercompression.api.CLNDecompressors;
import com.io7m.calino.validation.api.CLNValidationRequest;
import com.io7m.calino.vanilla.CLN1Validators;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.SecureRandom;

import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.READ;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class CLN1EmbeddedTest
{
  private CLNParsers parsers;
  private Path directory;
  private CLN1Validators validators;

  @BeforeEach
  public void setup()
    throws IOException
  {
    this.validators =
      new CLN1Validators();
    this.parsers =
      new CLNParsers();
    this.directory =
      CLNTestDirectories.createTempDirectory();
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    CLNTestDirectories.deleteDirectory(this.directory);
  }

  /**
   * Calino files embedded inside other files can be read.
   *
   * @throws Exception On errors
   */

  @Test
  public void testEmbedded()
    throws Exception
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1EmbeddedTest.class,
        this.directory,
        "basic-array-lz4.ctf"
      );

    final var rng =
      SecureRandom.getInstanceStrong();
    final var data =
      new byte[8192];

    final var paddedFile = this.directory.resolve("output.ctf");
    try (var output =
           Files.newOutputStream(
             paddedFile, CREATE, TRUNCATE_EXISTING, WRITE)) {
      rng.nextBytes(data);
      output.write(data);

      try (var input = Files.newInputStream(file)) {
        input.transferTo(output);
      }

      rng.nextBytes(data);
      output.write(data);
      output.flush();
    }

    try (var channel = FileChannel.open(paddedFile, READ)) {
      try (var bounded =
             new SubrangeSeekableByteChannel(
               channel, 8192L, Files.size(file))) {
        final var request =
          CLNParseRequest.builder(
            new CLNDecompressors(),
            bounded,
            paddedFile.toUri()
          ).build();

        try (var parser = this.parsers.createParser(request)) {
          final var parsed =
            parser.execute();
          final var validator =
            this.validators.createValidator(new CLNValidationRequest(
              parsed,
              paddedFile.toUri()));

          final var errors =
            validator.execute();

          assertEquals(0, errors.size());
        }
      }
    }
  }
}
