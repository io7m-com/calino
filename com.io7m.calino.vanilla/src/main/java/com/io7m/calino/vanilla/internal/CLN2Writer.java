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

import com.io7m.calino.api.CLNException;
import com.io7m.calino.api.CLNFileWritableType;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.calino.writer.api.CLNWriterType;
import com.io7m.jbssio.api.BSSWriterProviderType;

import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * The main writer implementation.
 */

public final class CLN2Writer
  implements CLNWriterType
{
  private final CLNWriteRequest request;
  private final BSSWriterProviderType writers;

  /**
   * The main writer implementation.
   *
   * @param inRequest The write request
   * @param inWriters A writer provider
   */

  public CLN2Writer(
    final BSSWriterProviderType inWriters,
    final CLNWriteRequest inRequest)
  {
    this.writers =
      Objects.requireNonNull(inWriters, "writers");
    this.request =
      Objects.requireNonNull(inRequest, "request");
  }

  @Override
  public CLNFileWritableType execute()
    throws CLNException
  {
    try {
      final var version = this.request.version();
      if (version.major() != 2L) {
        throw errorUnsupportedMajorVersion(version.major());
      }

      final var writer =
        this.writers.createWriterFromChannel(
          this.request.target(),
          this.request.channel(),
          "Main"
        );

      final CLN2FileWritable file =
        new CLN2FileWritable(this.writers, writer, this.request);

      file.start();
      return file;
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  @Override
  public void close()
  {
    // Nothing required.
  }

  private static CLNException errorUnsupportedMajorVersion(
    final long major)
  {
    return new CLNException(
      "Unsupported major version.",
      Map.ofEntries(
        Map.entry("Expected", "2"),
        Map.entry("Received", Long.toUnsignedString(major))
      ),
      "error-version-unsupported",
      Optional.empty()
    );
  }
}
