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

package com.io7m.calino.cmdline.internal;

import com.beust.jcommander.Parameter;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParserValidationEvent;
import com.io7m.calino.parser.api.CLNParsers;
import com.io7m.calino.supercompression.api.CLNDecompressors;
import com.io7m.calino.validation.api.CLNValidationError;
import com.io7m.calino.validation.api.CLNValidationStatus;
import com.io7m.claypot.core.CLPCommandContextType;
import com.io7m.claypot.core.CLPCommandType;
import com.io7m.jmulticlose.core.CloseableCollection;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.URI;
import java.nio.channels.FileChannel;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Optional;

import static java.nio.file.StandardOpenOption.READ;

/**
 * An abstract command that reads a single file.
 */

public abstract class CLNAbstractReadFileCommand
  extends CLNAbstractCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNAbstractReadFileCommand.class);

  private List<CLNValidationError> parserValidationErrors;
  private List<CLNValidationError> parserValidationWarnings;

  @Parameter(
    required = true,
    description = "The texture file",
    names = "--file")
  private Path file;

  /**
   * @param inContext The context
   */

  public CLNAbstractReadFileCommand(
    final CLPCommandContextType inContext)
  {
    super(Locale.getDefault(), inContext);
    this.parserValidationErrors = new ArrayList<>();
    this.parserValidationWarnings = new ArrayList<>();
  }

  @Override
  protected final CLPCommandType.Status executeActual()
    throws Exception
  {
    final var parsers = new CLNParsers();
    final var compressors = new CLNDecompressors();

    try (var resources = CloseableCollection.create()) {
      final var channel =
        resources.add(FileChannel.open(this.file, READ));
      final var request =
        CLNParseRequest.builder(compressors, channel, this.file.toUri())
          .setValidationReceiver(this::onValidationEvent)
          .build();
      final var parser =
        resources.add(parsers.createParser(request));
      final var fileParsed =
        resources.add(parser.execute());

      return this.executeWithReadFile(fileParsed);
    }
  }

  protected final List<CLNValidationError> parserValidationErrors()
  {
    return this.parserValidationErrors;
  }

  protected final List<CLNValidationError> parserValidationWarnings()
  {
    return this.parserValidationWarnings;
  }

  private void onValidationEvent(
    final CLNParserValidationEvent event)
  {
    if (event.isError()) {
      this.parserValidationErrors.add(
        new CLNValidationError(
          event.source(),
          event.offset(),
          CLNValidationStatus.STATUS_ERROR,
          Optional.of(event.id()),
          event.message(),
          Optional.empty()
        )
      );
    } else {
      this.parserValidationWarnings.add(
        new CLNValidationError(
          event.source(),
          event.offset(),
          CLNValidationStatus.STATUS_WARNING,
          Optional.of(event.id()),
          event.message(),
          Optional.empty()
        )
      );
    }
  }

  protected final URI source()
  {
    return this.file.toUri();
  }

  protected abstract Status executeWithReadFile(CLNFileReadableType fileParsed)
    throws IOException;
}
