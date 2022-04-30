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

import com.io7m.calino.api.CLNImageCubeFaceDeclaration;
import com.io7m.calino.api.CLNImageCubeMipMapDeclaration;
import com.io7m.calino.api.CLNImageCubeMipMapDeclarations;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class CLNImageCubeMipMapDeclarationsTest
{
  private static final CLNImageCubeFaceDeclaration FACE =
    new CLNImageCubeFaceDeclaration(10L, 10L, 0);

  /**
   * Empty mip map lists are well-formed.
   */

  @Test
  public void testEmpty()
  {
    final var ex = Assertions.assertThrows(
      IllegalArgumentException.class,
      () -> {
        new CLNImageCubeMipMapDeclarations(
          List.of(),
          0);
      });

    assertEquals(
      "Mip levels must be strictly increasing with all values present in the range [0, 0]",
      ex.getMessage()
    );
  }

  /**
   * Ordered lists are well-formed.
   */

  @Test
  public void testWellFormed()
  {
    Assertions.assertDoesNotThrow(() -> {
      new CLNImageCubeMipMapDeclarations(List.of(
        new CLNImageCubeMipMapDeclaration(
          2,
          FACE,
          FACE,
          FACE,
          FACE,
          FACE,
          FACE),
        new CLNImageCubeMipMapDeclaration(
          1,
          FACE,
          FACE,
          FACE,
          FACE,
          FACE,
          FACE),
        new CLNImageCubeMipMapDeclaration(0, FACE, FACE, FACE, FACE, FACE, FACE)
      ), 0);
    });
  }

  /**
   * Missing levels are invalid.
   */

  @Test
  public void testMissingLevel()
  {
    final var ex = Assertions.assertThrows(
      IllegalArgumentException.class,
      () -> {
        new CLNImageCubeMipMapDeclarations(
          List.of(
            new CLNImageCubeMipMapDeclaration(
              0,
              FACE, FACE, FACE, FACE, FACE, FACE),
            new CLNImageCubeMipMapDeclaration(
              2,
              FACE, FACE, FACE, FACE, FACE, FACE),
            new CLNImageCubeMipMapDeclaration(
              3,
              FACE, FACE, FACE, FACE, FACE, FACE)
          ),
          0);
      });
    assertEquals(
      "Mip levels must be strictly increasing with all values present in the range [0, 3]",
      ex.getMessage()
    );
  }

  /**
   * Duplicate levels are invalid.
   */

  @Test
  public void testDuplicateLevel()
  {
    final var ex = Assertions.assertThrows(
      IllegalArgumentException.class,
      () -> {
        new CLNImageCubeMipMapDeclarations(
          List.of(
            new CLNImageCubeMipMapDeclaration(
              0,
              FACE, FACE, FACE, FACE, FACE, FACE),
            new CLNImageCubeMipMapDeclaration(
              1,
              FACE, FACE, FACE, FACE, FACE, FACE),
            new CLNImageCubeMipMapDeclaration(
              2,
              FACE, FACE, FACE, FACE, FACE, FACE),
            new CLNImageCubeMipMapDeclaration(
              2,
              FACE, FACE, FACE, FACE, FACE, FACE),
            new CLNImageCubeMipMapDeclaration(
              3,
              FACE, FACE, FACE, FACE, FACE, FACE)
          ),
          0);
      });
    assertEquals("Duplicate mip level 2 specified", ex.getMessage());
  }

  /**
   * Levels in the wrong order are invalid.
   */

  @Test
  public void testWrongOrder0()
  {
    final var ex = Assertions.assertThrows(
      IllegalArgumentException.class,
      () -> {
        new CLNImageCubeMipMapDeclarations(
          List.of(
            new CLNImageCubeMipMapDeclaration(
              0,
              FACE, FACE, FACE, FACE, FACE, FACE),
            new CLNImageCubeMipMapDeclaration(
              1,
              FACE, FACE, FACE, FACE, FACE, FACE),
            new CLNImageCubeMipMapDeclaration(
              2,
              FACE, FACE, FACE, FACE, FACE, FACE),
            new CLNImageCubeMipMapDeclaration(
              3,
              FACE, FACE, FACE, FACE, FACE, FACE)
          ),
          0);
      });
    assertEquals(
      "Cube image mipmaps must be provided in sorted order!",
      ex.getMessage()
    );
  }
}
