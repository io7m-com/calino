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

package com.io7m.calino.tests;

import com.io7m.calino.supercompression.api.CLNDecompressors;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParseRequestBuilderType;
import com.io7m.calino.parser.api.CLNParserType;
import com.io7m.calino.parser.api.CLNParserValidationEvent;
import com.io7m.calino.vanilla.CLN1Parsers;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.ClosingResourceFailedException;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.channels.FileChannel;
import java.util.ArrayList;
import java.util.function.Consumer;

import static java.nio.file.StandardOpenOption.READ;

public final class CLN1ParsersFileTest extends CLN1ParsersContract
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN1ParsersFileTest.class);

  @BeforeEach
  public void setup()
    throws IOException
  {
    this.parsers = new CLN1Parsers();
    this.directory = CLNTestDirectories.createTempDirectory();
    this.resources = CloseableCollection.create();
    this.events = new ArrayList<>();
  }

  @AfterEach
  public void tearDown()
    throws IOException, ClosingResourceFailedException
  {
    CLNTestDirectories.deleteDirectory(this.directory);
    this.resources.close();
  }

  @Override
  public CLNParserType parserFor(
    final String name,
    final Consumer<CLNParseRequestBuilderType> configurator)
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        name
      );

    final var channel =
      FileChannel.open(file, READ);

    final var builder =
      CLNParseRequest.builder(new CLNDecompressors(), channel, file.toUri())
        .setValidationReceiver(this::onValidationEvent);

    configurator.accept(builder);

    final var parser =
      this.parsers.createParser(builder.build());

    return this.resources.add(parser);
  }

  private void onValidationEvent(
    final CLNParserValidationEvent event)
  {
    LOG.debug("event: {}", event);
    this.events.add(event);
  }
}
