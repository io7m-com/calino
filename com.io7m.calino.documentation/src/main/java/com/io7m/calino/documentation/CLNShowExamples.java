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

package com.io7m.calino.documentation;

import com.io7m.calino.cmdline.CLNMain;

import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.List;

import static java.nio.charset.StandardCharsets.*;
import static java.nio.file.StandardOpenOption.*;

/**
 * Generate example text.
 */

public final class CLNShowExamples
{
  private CLNShowExamples()
  {

  }

  /**
   * Command-line entry point.
   *
   * @param args The arguments
   *
   * @throws Exception On errors
   */

  public static void main(
    final String[] args)
    throws Exception
  {
    final var commands = List.of(
      "check",
      "create-2d",
      "create-array",
      "create-cube",
      "extract-image-data-2d",
      "extract-image-data-array",
      "extract-image-data-cube",
      "help",
      "show-image-info",
      "show-metadata",
      "show-sections",
      "show-summary",
      "show-version",
      "version"
    );

    for (final var command : commands) {
      final var path =
        Paths.get("c-" + command + ".txt");

      try (var output =
             Files.newOutputStream(path, CREATE, WRITE, TRUNCATE_EXISTING)) {
        System.setOut(new PrintStream(output, true, UTF_8));
        System.setErr(new PrintStream(output, true, UTF_8));
        CLNMain.mainExitless(new String[]{
          "help",
          command
        });
      }
    }
  }
}
