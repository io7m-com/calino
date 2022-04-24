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

import com.io7m.calino.api.CLNImageArrayMipMapDeclaration;
import com.io7m.calino.api.CLNImageArrayMipMapDeclarations;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class CLNImageArrayMipMapDeclarationsTest
{
  /**
   * Empty mip map lists are invalid.
   */

  @Test
  public void testEmpty()
  {
    final var ex = Assertions.assertThrows(
      IllegalArgumentException.class,
      () -> {
        new CLNImageArrayMipMapDeclarations(
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
      new CLNImageArrayMipMapDeclarations(List.of(
        new CLNImageArrayMipMapDeclaration(2, 0, 0L, 0L, 0),
        new CLNImageArrayMipMapDeclaration(2, 1, 0L, 0L, 0),
        new CLNImageArrayMipMapDeclaration(2, 2, 0L, 0L, 0),
        new CLNImageArrayMipMapDeclaration(1, 0, 0L, 0L, 0),
        new CLNImageArrayMipMapDeclaration(1, 1, 0L, 0L, 0),
        new CLNImageArrayMipMapDeclaration(1, 2, 0L, 0L, 0),
        new CLNImageArrayMipMapDeclaration(0, 0, 0L, 0L, 0),
        new CLNImageArrayMipMapDeclaration(0, 1, 0L, 0L, 0),
        new CLNImageArrayMipMapDeclaration(0, 2, 0L, 0L, 0)
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
        new CLNImageArrayMipMapDeclarations(
          List.of(
            new CLNImageArrayMipMapDeclaration(
              2,
              0,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              0,
              0L,
              0L,
              0)
          ),
          0);
      });

    assertEquals(
      "Mip levels must be strictly increasing with all values present in the range [0, 2]",
      ex.getMessage()
    );
  }

  /**
   * Missing layers are invalid.
   */

  @Test
  public void testMissingLayer()
  {
    final var ex = Assertions.assertThrows(
      IllegalArgumentException.class,
      () -> {
        new CLNImageArrayMipMapDeclarations(
          List.of(
            new CLNImageArrayMipMapDeclaration(
              1,
              0,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              1,
              2,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              0,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              1,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              2,
              0L,
              0L,
              0)
          ),
          0);
      });
    assertEquals(
      "Mip layers for level 1 must be strictly increasing with all values present in the range [0, 2]",
      ex.getMessage());
  }

  /**
   * Duplicate layers are invalid.
   */

  @Test
  public void testDuplicateLayer()
  {
    final var ex = Assertions.assertThrows(
      IllegalArgumentException.class,
      () -> {
        new CLNImageArrayMipMapDeclarations(
          List.of(
            new CLNImageArrayMipMapDeclaration(
              1,
              0,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              1,
              0,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              1,
              1,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              1,
              2,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              0,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              1,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              2,
              0L,
              0L,
              0)
          ),
          0);
      });

    assertEquals(
      "Mip level 1 layer 0 is not unique",
      ex.getMessage()
    );
  }

  /**
   * Layers in the wrong order are invalid.
   */

  @Test
  public void testWrongOrder0()
  {
    final var ex = Assertions.assertThrows(
      IllegalArgumentException.class,
      () -> {
        new CLNImageArrayMipMapDeclarations(
          List.of(
            new CLNImageArrayMipMapDeclaration(
              1,
              2,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              1,
              1,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              1,
              0,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              2,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              1,
              0L,
              0L,
              0),
            new CLNImageArrayMipMapDeclaration(
              0,
              0,
              0L,
              0L,
              0)
          ),
          0);
      });
    assertEquals(
      "Array image mipmaps must be provided in sorted order!",
      ex.getMessage());
  }
}
