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

import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.api.CLNSectionDescription;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParserType;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The main parser implementation.
 */

public final class CLN1Parser implements CLNParserType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN1Parser.class);

  private final CLNParseRequest request;
  private final BSSReaderRandomAccessType reader;
  private final AtomicBoolean closed;

  /**
   * The main parser implementation.
   *
   * @param inRequest The read request
   * @param inReader  A reader
   */

  public CLN1Parser(
    final CLNParseRequest inRequest,
    final BSSReaderRandomAccessType inReader)
  {
    this.request =
      Objects.requireNonNull(inRequest, "request");
    this.reader =
      Objects.requireNonNull(inReader, "reader");
    this.closed =
      new AtomicBoolean(false);
  }

  @Override
  public CLNFileReadableType execute()
    throws IOException
  {
    this.reader.seekTo(0L);

    final var identifier =
      this.reader.readU64BE("identifier");
    final var major =
      this.reader.readU32BE("versionMajor");
    final var minor =
      this.reader.readU32BE("versionMinor");

    if (identifier != CLNIdentifiers.fileIdentifier()) {
      throw new IOException(this.errorMagicNumber(identifier));
    }
    if (major != 1L) {
      throw new IOException(this.errorUnsupportedMajorVersion(major));
    }

    final var fileSections =
      new ArrayList<CLNFileSectionDescription>();

    while (true) {
      final var remainingOpt = this.reader.bytesRemaining();
      if (remainingOpt.isPresent()) {
        if (remainingOpt.getAsLong() == 0L) {
          LOG.warn(
            "encountered EOF before encountering an 'end' section; file is likely truncated/damaged");
          break;
        }
      }

      final var fileOffset =
        this.reader.offsetCurrentAbsolute();
      final var sectionId =
        this.reader.readU64BE("sectionId");
      final var sectionSize =
        this.reader.readU64BE("sectionSize");

      fileSections.add(
        new CLNFileSectionDescription(
          fileOffset,
          new CLNSectionDescription(sectionId, sectionSize))
      );

      this.reader.skip(sectionSize);
      if (sectionId == CLNIdentifiers.sectionEndIdentifier()) {
        break;
      }
    }

    this.closed.set(true);
    return new CLN1FileReadable(
      this.request.decompressors(),
      this.reader,
      this.request,
      new CLNVersion((int) major, (int) minor),
      fileSections,
      this.reader.bytesRemaining().orElse(0L)
    );
  }

  private String errorUnsupportedMajorVersion(
    final long major)
  {
    final var lineSeparator = System.lineSeparator();
    return new StringBuilder(64)
      .append("Unrecognized major version.")
      .append(lineSeparator)
      .append("  File: ")
      .append(this.request.source())
      .append(lineSeparator)
      .append("  Received: Major version ")
      .append(Long.toUnsignedString(major))
      .append(lineSeparator)
      .append("  Expected: Major version 1")
      .append(lineSeparator)
      .toString();
  }

  private String errorMagicNumber(
    final long identifier)
  {
    final var lineSeparator = System.lineSeparator();
    return new StringBuilder(64)
      .append("Unrecognized file identifier.")
      .append(lineSeparator)
      .append("  File: ")
      .append(this.request.source())
      .append(lineSeparator)
      .append("  Received: 0x")
      .append(Long.toUnsignedString(identifier, 16))
      .append(lineSeparator)
      .append("  Expected: ")
      .append(Long.toUnsignedString(CLNIdentifiers.fileIdentifier(), 16))
      .append(lineSeparator)
      .toString();
  }

  @Override
  public void close()
    throws IOException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.reader.close();
    }
  }
}
