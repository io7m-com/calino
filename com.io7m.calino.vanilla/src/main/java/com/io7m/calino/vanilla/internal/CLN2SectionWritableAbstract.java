/*
 * Copyright © 2026 Mark Raynsford <code@io7m.com> https://www.io7m.com
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
import com.io7m.calino.api.CLNSectionWritableType;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.jbssio.vanilla.BSSWriters;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.wendover.core.UncloseableSeekableByteChannel;

import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.channels.SeekableByteChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Objects;

import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

abstract class CLN2SectionWritableAbstract
  implements CLNSectionWritableType
{
  private static final BSSWriterProviderType WRITERS =
    new BSSWriters();

  private final Path file;
  private final FileChannel channel;
  private final CloseableCollectionType<CLNException> resources;
  private final CLNOnCloseOperationType<CLN2SectionWritableAbstract> onClose;
  private final long identifier;
  private final BSSWriterRandomAccessType writer;
  private SeekableByteChannel dataStream;

  protected CLN2SectionWritableAbstract(
    final long inIdentifier,
    final CloseableCollectionType<CLNException> inResources,
    final CLNOnCloseOperationType<CLN2SectionWritableAbstract> inOnClose)
    throws IOException
  {
    this.identifier =
      inIdentifier;
    this.resources =
      Objects.requireNonNull(inResources, "Resources");
    this.onClose =
      Objects.requireNonNull(inOnClose, "OnClose");
    this.file =
      Files.createTempFile("calino-", ".bin");
    this.channel =
      FileChannel.open(
        this.file,
        CREATE,
        WRITE,
        TRUNCATE_EXISTING
      );
    this.writer =
      WRITERS.createWriterFromChannel(
        this.file.toUri(),
        this.channel,
        "Main"
      );

    this.resources.add(this.channel::close);
    this.resources.add(() -> Files.deleteIfExists(this.file));
  }

  protected final BSSWriterRandomAccessType writer()
  {
    return this.writer;
  }

  public final SeekableByteChannel sectionData()
  {
    if (this.dataStream == null) {
      throw new IllegalArgumentException("Section has not been closed yet.");
    }
    return this.dataStream;
  }

  @Override
  public final long identifier()
  {
    return this.identifier;
  }

  @Override
  public final void close()
    throws CLNException
  {
    try {
      this.channel.force(true);
      this.dataStream = Files.newByteChannel(this.file);
      this.onClose.execute(this);
    } catch (final IOException e) {
      throw CLNException.wrap(e);
    }
  }

  @Override
  public final SeekableByteChannel sectionDataChannel()
  {
    return new UncloseableSeekableByteChannel(this.channel);
  }
}
