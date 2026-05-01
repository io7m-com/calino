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

import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParsers;
import com.io7m.calino.supercompression.api.CLNDecompressors;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType;

import java.net.URI;
import java.nio.channels.FileChannel;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static java.nio.file.StandardOpenOption.READ;

/**
 * An abstract command that reads a single file.
 */

public abstract class CLNAbstractReadFileCommand
  extends CLNAbstractCommand
{
  private static final QParameterNamed1<Path> FILE =
    new QParameterNamed1<>(
      "--file",
      List.of(),
      new QStringType.QConstant("The texture file."),
      Optional.empty(),
      Path.class
    );

  CLNAbstractReadFileCommand(
    final QCommandMetadata inMetadata)
  {
    super(
      inMetadata
    );
  }

  protected abstract List<QParameterNamedType<?>> onListNamedParametersWithFile();

  @Override
  public final List<QParameterNamedType<?>> onListNamedParametersActual()
  {
    final var parameters = new ArrayList<QParameterNamedType<?>>();
    parameters.add(FILE);
    parameters.addAll(this.onListNamedParametersWithFile());
    return List.copyOf(parameters);
  }

  @Override
  public final QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var parsers =
      new CLNParsers();
    final var compressors =
      new CLNDecompressors();
    final var file =
      context.parameterValue(FILE);

    try (var resources = CloseableCollection.create()) {
      final var channel =
        resources.add(FileChannel.open(file, READ));
      final var request =
        CLNParseRequest.builder(compressors, channel, file.toUri())
          .build();
      final var parser =
        resources.add(parsers.createParser(request));
      final var fileParsed =
        resources.add(parser.execute());

      return this.executeWithReadFile(context, fileParsed);
    }
  }

  protected static URI source(
    final QCommandContextType context)
  {
    return context.parameterValue(FILE).toUri();
  }

  protected abstract QCommandStatus executeWithReadFile(
    QCommandContextType context,
    CLNFileReadableType fileParsed)
    throws Exception;
}
