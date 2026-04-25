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

import com.io7m.calino.parser.api.CLNProbes;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.jmulticlose.core.ClosingResourceFailedException;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.file.Path;

import static java.nio.file.StandardOpenOption.READ;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class CLNProbesTest
{
  private Path directory;
  private CloseableCollectionType<ClosingResourceFailedException> resources;
  private CLNProbes probes;

  @BeforeEach
  public void setup()
    throws IOException
  {
    this.probes = new CLNProbes();
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

  @Test
  public void testVersion1()
    throws IOException
  {
    final var file =
      this.fileOf("basic.ctf");
    final var channel =
      FileChannel.open(file, READ);

    final var probe =
      this.probes.createProbe(file.toUri(), channel);
    final var version =
      probe.execute();

    assertEquals(1, version.major());
    assertEquals(0, version.minor());
  }

  @Test
  public void testBrokenFileIdentifier()
    throws IOException
  {
    final var file =
      this.fileOf("broken-bad-identifier.ctf");
    final var channel =
      FileChannel.open(file, READ);

    final var probe =
      this.probes.createProbe(file.toUri(), channel);

    final var ex = assertThrows(IOException.class, probe::execute);
    assertTrue(ex.getMessage().contains("Unrecognized file identifier"));
  }

  @Test
  public void testBrokenTruncated()
    throws IOException
  {
    final var file =
      this.fileOf("broken-truncated.ctf");
    final var channel =
      FileChannel.open(file, READ);

    final var probe =
      this.probes.createProbe(file.toUri(), channel);

    final var ex = assertThrows(IOException.class, probe::execute);
    assertTrue(ex.getMessage().contains("File is truncated."));
  }

  @Test
  public void testBrokenTruncated1()
    throws IOException
  {
    final var file =
      this.fileOf("broken-truncated-1.ctf");
    final var channel =
      FileChannel.open(file, READ);

    final var probe =
      this.probes.createProbe(file.toUri(), channel);

    final var ex = assertThrows(IOException.class, probe::execute);
    assertTrue(ex.getMessage().contains("File is truncated."));
  }

  @Test
  public void testBrokenTruncated2()
    throws IOException
  {
    final var file =
      this.fileOf("broken-truncated-2.ctf");
    final var channel =
      FileChannel.open(file, READ);

    final var probe =
      this.probes.createProbe(file.toUri(), channel);

    final var ex = assertThrows(IOException.class, probe::execute);
    assertTrue(ex.getMessage().contains("File is truncated."));
  }

  private Path fileOf(final String name)
    throws IOException
  {
    return CLNTestDirectories.resourceOf(
      CLNProbesTest.class,
      this.directory,
      name
    );
  }
}
