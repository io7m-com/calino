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

import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.parser.api.CLNParseRequestBuilderType;
import com.io7m.calino.parser.api.CLNParserType;
import com.io7m.calino.supercompression.api.CLNDecompressors;
import com.io7m.calino.vanilla.CLN1Parsers;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.ClosingResourceFailedException;
import com.io7m.wendover.core.internal.ByteBufferChannel;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;

import java.io.IOException;
import java.nio.channels.FileChannel;
import java.util.function.Consumer;

import static java.nio.file.StandardOpenOption.READ;

public final class CLN1ParsersMappedTest extends CLN1ParsersContract
{
  @BeforeEach
  public void setup()
    throws IOException
  {
    this.parsers = new CLN1Parsers();
    this.directory = CLNTestDirectories.createTempDirectory();
    this.resources = CloseableCollection.create();
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

    this.resources.add(channel);

    final var map =
      channel.map(FileChannel.MapMode.READ_ONLY, 0L, channel.size());

    final var mappedChannel =
      new ByteBufferChannel(map);

    this.resources.add(mappedChannel);

    final var builder =
      CLNParseRequest.builder(new CLNDecompressors(), channel, file.toUri());

    configurator.accept(builder);

    final var parser =
      this.parsers.createParser(builder.build());

    return this.resources.add(parser);
  }
}
