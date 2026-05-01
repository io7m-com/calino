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
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParserType;
import com.io7m.calino.vanilla.CLNFileFormats;
import com.io7m.entomos.core.EoFileReaderFactoryType;
import com.io7m.entomos.core.EoFileReaderType;
import com.io7m.entomos.core.EoFileVersionsDescription;
import com.io7m.jbssio.api.BSSReaderProviderType;

import java.util.Objects;
import java.util.OptionalLong;

/**
 * The main parser implementation.
 */

public final class CLN2Parser
  implements CLNParserType
{
  private final CLNParseRequest request;
  private final EoFileReaderFactoryType<EoFileVersionsDescription> readers;
  private final BSSReaderProviderType bssReaders;
  private final EoFileReaderFactoryType<Void> readersUnchecked;

  /**
   * The main parser implementation.
   *
   * @param inRequest          The read request
   * @param inBSSReaders       The BSS reader factory
   * @param inReadersChecked   A checked reader factory
   * @param inReadersUnchecked An unchecked reader factory
   */

  public CLN2Parser(
    final CLNParseRequest inRequest,
    final BSSReaderProviderType inBSSReaders,
    final EoFileReaderFactoryType<EoFileVersionsDescription> inReadersChecked,
    final EoFileReaderFactoryType<Void> inReadersUnchecked)
  {
    this.request =
      Objects.requireNonNull(inRequest, "Request");
    this.readers =
      Objects.requireNonNull(inReadersChecked, "Readers");
    this.bssReaders =
      Objects.requireNonNull(inBSSReaders, "BSSReaders");
    this.readersUnchecked =
      Objects.requireNonNull(inReadersUnchecked, "ReadersUnchecked");
  }

  @Override
  public CLNFileReadableType execute()
    throws CLNException
  {
    try {
      final var bssReader =
        this.bssReaders.createReaderFromChannel(
          this.request.source(),
          this.request.channel(),
          "Main",
          OptionalLong.of(this.request.channel().size())
        );

      final EoFileReaderType reader =
        switch (this.request.strictness()) {
          case PARSE_STRICT -> {
            yield this.readers.forChannel(
              this.request.source(),
              CLNIdentifiers.fileIdentifier(),
              CLNIdentifiers.sectionEndIdentifier(),
              this.request.channel(),
              CLNFileFormats.fileFormats()
            );
          }
          case PARSE_PERMISSIVE -> {
            yield this.readersUnchecked.forChannel(
              this.request.source(),
              CLNIdentifiers.fileIdentifier(),
              CLNIdentifiers.sectionEndIdentifier(),
              this.request.channel(),
              null
            );
          }
        };

      return new CLN2FileReadable(
        this.request.decompressors(),
        bssReader,
        reader,
        this.request
      );
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }

  @Override
  public void close()
  {
    // Nothing required.
  }
}
