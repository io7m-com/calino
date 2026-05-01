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

package com.io7m.calino.vanilla;

import com.io7m.calino.api.CLNException;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParserFactoryType;
import com.io7m.calino.parser.api.CLNParserType;
import com.io7m.calino.vanilla.internal.CLN2Parser;
import com.io7m.entomos.core.EoFileReaderFactoryType;
import com.io7m.entomos.core.EoFileReadersChecked;
import com.io7m.entomos.core.EoFileReadersUnchecked;
import com.io7m.entomos.core.EoFileVersionsDescription;
import com.io7m.jbssio.api.BSSReaderProviderType;

import java.util.Objects;
import java.util.ServiceConfigurationError;
import java.util.ServiceLoader;

/**
 * A parser factory supporting major version 2.
 */

public final class CLN2Parsers implements CLNParserFactoryType
{
  private final BSSReaderProviderType readers;
  private final EoFileReaderFactoryType<EoFileVersionsDescription> readersChecked;
  private final EoFileReaderFactoryType<Void> readersUnchecked;

  /**
   * A parser factory supporting major version 2.
   */

  public CLN2Parsers()
  {
    this(loadReadersFromServiceLoader());
  }

  /**
   * A parser factory supporting major version 2.
   *
   * @param inReaders A provider of readers
   */

  public CLN2Parsers(
    final BSSReaderProviderType inReaders)
  {
    this.readers =
      Objects.requireNonNull(inReaders, "Readers");
    this.readersChecked =
      new EoFileReadersChecked(this.readers);
    this.readersUnchecked =
      new EoFileReadersUnchecked(this.readers);
  }

  private static BSSReaderProviderType loadReadersFromServiceLoader()
  {
    return ServiceLoader.load(BSSReaderProviderType.class)
      .findFirst()
      .orElseThrow(() -> new ServiceConfigurationError(
        "No services available of type %s".formatted(BSSReaderProviderType.class))
      );
  }

  @Override
  public int supportedMajorVersion()
  {
    return 2;
  }

  @Override
  public int highestMinorVersion()
  {
    return 0;
  }

  @Override
  public CLNParserType createParser(
    final CLNParseRequest request)
    throws CLNException
  {
    try {
      return new CLN2Parser(
        request,
        this.readers,
        this.readersChecked,
        this.readersUnchecked
      );
    } catch (final Exception e) {
      throw CLNException.wrap(e);
    }
  }
}
