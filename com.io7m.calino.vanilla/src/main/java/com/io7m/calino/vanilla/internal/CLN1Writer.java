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

import com.io7m.calino.api.CLNFileWritableType;
import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.calino.writer.api.CLNWriterType;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;

import java.io.IOException;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

public final class CLN1Writer implements CLNWriterType
{
  private final CLNWriteRequest request;
  private final BSSWriterRandomAccessType writer;
  private final AtomicBoolean closed;
  private final BSSWriterProviderType writers;

  public CLN1Writer(
    final BSSWriterProviderType inWriters,
    final CLNWriteRequest inRequest,
    final BSSWriterRandomAccessType inWriter)
  {
    this.writers =
      Objects.requireNonNull(inWriters, "writers");
    this.request =
      Objects.requireNonNull(inRequest, "request");
    this.writer =
      Objects.requireNonNull(inWriter, "writer");
    this.closed =
      new AtomicBoolean(false);
  }

  @Override
  public CLNFileWritableType execute()
    throws IOException
  {
    final var version = this.request.version();
    if (version.major() != 1L) {
      throw new IOException(this.errorUnsupportedMajorVersion(version.major()));
    }

    this.writer.seekTo(0L);
    this.writer.writeU64BE(CLNIdentifiers.fileIdentifier());
    this.writer.writeU32BE(version.major());
    this.writer.writeU32BE(version.minor());

    this.closed.set(true);
    return new CLN1FileWritable(this.writers, this.writer, this.request);
  }

  @Override
  public void close()
    throws IOException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.writer.close();
    }
  }

  private String errorUnsupportedMajorVersion(
    final long major)
  {
    final var lineSeparator = System.lineSeparator();
    return new StringBuilder(64)
      .append("Unsupported major version.")
      .append(lineSeparator)
      .append("  File: ")
      .append(this.request.target())
      .append("  Received: Major version ")
      .append(Long.toUnsignedString(major))
      .append(lineSeparator)
      .append("  Expected: Major version 1")
      .append(lineSeparator)
      .toString();
  }
}
