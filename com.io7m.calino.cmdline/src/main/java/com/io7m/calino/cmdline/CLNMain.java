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

package com.io7m.calino.cmdline;

import com.io7m.calino.cmdline.internal.CLNChannelsLayoutDescriptionConverter;
import com.io7m.calino.cmdline.internal.CLNCommandCheck;
import com.io7m.calino.cmdline.internal.CLNCommandCreate2D;
import com.io7m.calino.cmdline.internal.CLNCommandCreateArray;
import com.io7m.calino.cmdline.internal.CLNCommandCreateCube;
import com.io7m.calino.cmdline.internal.CLNCommandExtractImageData2D;
import com.io7m.calino.cmdline.internal.CLNCommandExtractImageDataArray;
import com.io7m.calino.cmdline.internal.CLNCommandExtractImageDataCube;
import com.io7m.calino.cmdline.internal.CLNCommandShowImageInfo;
import com.io7m.calino.cmdline.internal.CLNCommandShowMetadata;
import com.io7m.calino.cmdline.internal.CLNCommandShowSections;
import com.io7m.calino.cmdline.internal.CLNCommandShowSummary;
import com.io7m.calino.cmdline.internal.CLNCommandShowVersion;
import com.io7m.calino.cmdline.internal.CLNStrings;
import com.io7m.calino.cmdline.internal.CLNSuperCompressionMethodConverter;
import com.io7m.calino.cmdline.internal.CLNVersionConverter;
import com.io7m.quarrel.core.QApplication;
import com.io7m.quarrel.core.QApplicationMetadata;
import com.io7m.quarrel.core.QApplicationType;
import com.io7m.quarrel.core.QValueConverterDirectory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.net.URI;
import java.util.List;
import java.util.Locale;
import java.util.Objects;
import java.util.Optional;

/**
 * The main command-line entry point.
 */

public final class CLNMain implements Runnable
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNMain.class);

  private final List<String> args;
  private final QApplicationType application;
  private int exitCode;

  /**
   * The main entry point.
   *
   * @param inArgs Command-line arguments
   */

  public CLNMain(
    final String[] inArgs)
  {
    this.args =
      Objects.requireNonNull(List.of(inArgs), "Command line arguments");

    final var metadata =
      new QApplicationMetadata(
        "calino",
        "com.io7m.calino",
        CLNMainVersion.MAIN_VERSION,
        CLNMainVersion.MAIN_BUILD,
        "The calino command-line application.",
        Optional.of(URI.create("https://www.io7m.com/software/calino/"))
      );

    final var builder =
      QApplication.builder(metadata);

    try {
      builder.setApplicationResources(
        new CLNStrings(Locale.getDefault()).resources());
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }

    builder.setValueConverters(
      QValueConverterDirectory.core()
        .with(new CLNChannelsLayoutDescriptionConverter())
        .with(new CLNSuperCompressionMethodConverter())
        .with(new CLNVersionConverter())
    );

    builder.addCommand(new CLNCommandCheck());
    builder.addCommand(new CLNCommandCreate2D());
    builder.addCommand(new CLNCommandCreateArray());
    builder.addCommand(new CLNCommandCreateCube());
    builder.addCommand(new CLNCommandExtractImageData2D());
    builder.addCommand(new CLNCommandExtractImageDataArray());
    builder.addCommand(new CLNCommandExtractImageDataCube());
    builder.addCommand(new CLNCommandShowImageInfo());
    builder.addCommand(new CLNCommandShowMetadata());
    builder.addCommand(new CLNCommandShowSections());
    builder.addCommand(new CLNCommandShowSummary());
    builder.addCommand(new CLNCommandShowVersion());

    builder.allowAtSyntax(true);

    this.application = builder.build();
    this.exitCode = 0;
  }

  /**
   * The main entry point.
   *
   * @param args Command line arguments
   */

  public static void main(
    final String[] args)
  {
    System.exit(mainExitless(args));
  }

  /**
   * The main (exitless) entry point.
   *
   * @param args Command line arguments
   *
   * @return The exit code
   */

  public static int mainExitless(
    final String[] args)
  {
    final CLNMain cm = new CLNMain(args);
    cm.run();
    return cm.exitCode();
  }

  /**
   * @return The quarrel application
   */

  public QApplicationType application()
  {
    return this.application;
  }

  /**
   * @return The program exit code
   */

  public int exitCode()
  {
    return this.exitCode;
  }

  @Override
  public void run()
  {
    this.exitCode = this.application.run(LOG, this.args).exitCode();
  }

  @Override
  public String toString()
  {
    return String.format(
      "[CLNMain 0x%s]",
      Long.toUnsignedString(System.identityHashCode(this), 16)
    );
  }
}
