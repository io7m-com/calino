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
import com.io7m.calino.api.CLNSectionReadableType;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.entomos.core.EoFileSection;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;
import com.io7m.seltzer.io.SIOException;
import com.io7m.wendover.core.ReadOnlySeekableByteChannel;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * An abstract readable section.
 */

public abstract class CLN2SectionReadableAbstract
  implements CLNSectionReadableType
{
  private final BSSReaderRandomAccessType reader;
  private final CLNParseRequest request;
  private final EoFileSection section;

  protected CLN2SectionReadableAbstract(
    final BSSReaderRandomAccessType inReader,
    final CLNParseRequest inRequest,
    final EoFileSection inSection)
  {
    this.reader =
      Objects.requireNonNull(inReader, "Reader");
    this.request =
      Objects.requireNonNull(inRequest, "Request");
    this.section =
      Objects.requireNonNull(inSection, "Section");
  }

  @Override
  public final EoFileSection section()
  {
    return this.section;
  }

  protected final CLNParseRequest request()
  {
    return this.request;
  }

  protected final BSSReaderRandomAccessType reader()
  {
    return this.reader;
  }

  protected final BSSReaderRandomAccessType sectionDataReader()
    throws SIOException
  {
    return this.reader.createSubReaderAtBounded(
      "SectionData",
      this.section.dataOffset(),
      this.section.dataSize()
    );
  }

  @Override
  public final SeekableByteChannel sectionDataChannel()
    throws CLNException
  {
    try {
      final var baseReadable =
        new ReadOnlySeekableByteChannel(this.request.channel());

      final var channel =
        new SubrangeSeekableByteChannel(
          baseReadable,
          this.section.dataOffset(),
          this.section.dataSize()
        );

      channel.position(0L);
      return channel;
    } catch (final IOException e) {
      throw CLNException.wrap(e);
    }
  }

  @Override
  public final void close()
  {

  }

  protected final CLNException errorLimitExceeded(
    final long length,
    final long limit,
    final String limitName)
  {
    final String offsetText =
      "0x" + Long.toUnsignedString(
        this.reader().offsetCurrentAbsolute(),
        16);

    return new CLNException(
      "Limit exceeded.",
      Map.ofEntries(
        Map.entry("File Offset", offsetText),
        Map.entry("Limit (Name)", limitName),
        Map.entry("Limit (Value)", Long.toUnsignedString(limit)),
        Map.entry("Received", Long.toUnsignedString(length))
      ),
      "error-limit-exceeded",
      Optional.empty()
    );
  }
}
