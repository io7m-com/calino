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

import com.io7m.calino.api.CLNSectionWritableType;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.wendover.core.CloseShieldSeekableByteChannel;
import com.io7m.wendover.core.SubrangeSeekableByteChannel;
import com.io7m.wendover.core.UpperRangeTrackingSeekableByteChannel;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.channels.SeekableByteChannel;
import java.util.Objects;

/**
 * A writable section.
 */

public abstract class CLN1SectionWritableAbstract
  implements CLNSectionWritableType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN1SectionWritableAbstract.class);

  private final BSSWriterRandomAccessType writer;
  private final CLNWriteRequest request;
  private final long identifier;
  private final CLNOnCloseOperationType<CLNSectionWritableType> onClose;
  private final long offsetStartData;
  private final long offsetStart;
  private long wrote;

  /**
   * A writable section.
   *
   * @param inOnClose    A function executed on closing
   * @param inRequest    A write request
   * @param inIdentifier An identifier
   * @param inWriter     A writer
   */

  public CLN1SectionWritableAbstract(
    final BSSWriterRandomAccessType inWriter,
    final CLNWriteRequest inRequest,
    final long inIdentifier,
    final CLNOnCloseOperationType<CLNSectionWritableType> inOnClose)
  {
    this.writer =
      Objects.requireNonNull(inWriter, "writer");
    this.request =
      Objects.requireNonNull(inRequest, "request");
    this.identifier =
      inIdentifier;
    this.onClose =
      Objects.requireNonNull(inOnClose, "inOnClose");

    this.offsetStart =
      this.writer.offsetCurrentAbsolute();
    this.offsetStartData =
      this.offsetStart + 16L;
  }

  @Override
  public final long identifier()
  {
    return this.identifier;
  }

  protected final long offsetStartData()
  {
    return this.offsetStartData;
  }

  protected final long offsetStart()
  {
    return this.offsetStart;
  }

  protected final CLNWriteRequest request()
  {
    return this.request;
  }

  @Override
  public final SeekableByteChannel sectionDataChannel()
    throws IOException
  {
    final var startOffset =
      this.writer.offsetCurrentAbsolute();
    final var channel =
      this.request().channel();

    channel.position(this.offsetStartData);

    final var closeShield =
      new CloseShieldSeekableByteChannel(channel);
    final var upperTracker =
      new UpperRangeTrackingSeekableByteChannel(closeShield);

    return new SubrangeSeekableByteChannel(
      upperTracker,
      startOffset,
      Long.MAX_VALUE - startOffset,
      context -> {
        this.wrote = upperTracker.uppermostWritten() - startOffset;
      }
    );
  }

  @Override
  public final void close()
    throws IOException
  {
    this.writer.seekTo(this.offsetStart);
    this.writer.skip(16L);
    this.writer.skip(this.wrote);
    this.writer.align(16);

    final var size =
      this.writer.offsetCurrentAbsolute() - this.offsetStartData;

    this.writer.seekTo(this.offsetStart);
    this.writer.skip(8L);
    this.writer.writeU64BE(size);
    this.writer.skip(this.wrote);
    this.writer.align(16);

    this.onClose.execute(this);
  }
}
