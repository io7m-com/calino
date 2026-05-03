/*
 * Copyright © 2026 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

import com.io7m.calino.api.CLNByteOrder;
import com.io7m.calino.imageproc.api.CLNImageProcessorRequest;
import com.io7m.calino.imageproc.awt.CLNImageProcessorsAWT;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Path;
import java.util.Optional;
import java.util.Set;

import static com.io7m.calino.api.CLNImageFlagStandard.ALPHA_PREMULTIPLIED;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class CLNImageProcessorAWTTest
{
  private CLNImageProcessorsAWT processors;

  @BeforeEach
  public void setup()
  {
    this.processors =
      new CLNImageProcessorsAWT();
  }

  /**
   * Premultiplying alpha works.
   *
   * @param directory The directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testPremultiply(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLNImageProcessorAWTTest.class,
        directory,
        "fadePremultiply.png"
      );

    final var request =
      new CLNImageProcessorRequest(
        file,
        true,
        CLNByteOrder.LITTLE_ENDIAN,
        Optional.empty(),
        Optional.empty()
      );

    final var chain =
      this.processors.createProcessor(request)
        .process();

    assertEquals(
      Set.of(ALPHA_PREMULTIPLIED),
      chain.imageInfo().flags()
    );

    final var bytes =
      chain.mipMapUncompressedBytes(0);

    CLNHexDump.dumpTo(bytes, System.out);
    assertEquals(0xff, bytes[0] & 0xff);
    assertEquals(0x00, bytes[bytes.length - 1] & 0xff);

    for (int index = 0; index < bytes.length; index += 4) {
      final var r = bytes[index + 0];
      final var g = bytes[index + 1];
      final var b = bytes[index + 2];
      final var a = bytes[index + 3];
      assertEquals(r, a);
    }
  }

  /**
   * Premultiplying without alpha does nothing.
   *
   * @param directory The directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testPremultiplyNoAlpha(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLNImageProcessorAWTTest.class,
        directory,
        "fadeNoAlpha.png"
      );

    final var request =
      new CLNImageProcessorRequest(
        file,
        true,
        CLNByteOrder.LITTLE_ENDIAN,
        Optional.empty(),
        Optional.empty()
      );

    final var chain =
      this.processors.createProcessor(request)
        .process();

    assertEquals(
      Set.of(),
      chain.imageInfo().flags()
    );

    final var bytes =
      chain.mipMapUncompressedBytes(0);

    CLNHexDump.dumpTo(bytes, System.out);
    assertEquals(0xff, bytes[0] & 0xff);
    assertEquals(0x00, bytes[bytes.length - 1] & 0xff);

    for (int index = 0; index < bytes.length; index += 3) {
      final var r = bytes[index + 0];
      final var g = bytes[index + 1];
      final var b = bytes[index + 2];
      assertEquals(r, g);
      assertEquals(g, b);
    }
  }
}
