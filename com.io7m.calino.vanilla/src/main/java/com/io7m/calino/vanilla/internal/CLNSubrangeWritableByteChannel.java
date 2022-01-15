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

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.NonReadableChannelException;
import java.nio.channels.SeekableByteChannel;
import java.util.Objects;

public final class CLNSubrangeWritableByteChannel
  implements SeekableByteChannel
{
  private final SeekableByteChannel delegate;
  private final long baseStart;
  private final long limit;
  private final CLNOnCloseOperationType<CLNSubrangeWritableByteChannel> onClose;
  private long uppermost;

  public CLNSubrangeWritableByteChannel(
    final SeekableByteChannel inDelegate,
    final long inBase,
    final long inLimit,
    final CLNOnCloseOperationType<CLNSubrangeWritableByteChannel> inOnClose)
  {
    this.delegate =
      Objects.requireNonNull(inDelegate, "delegate");
    this.onClose =
      Objects.requireNonNull(inOnClose, "inOnClose");

    this.baseStart = inBase;
    this.uppermost = 0L;
    this.limit = inLimit;
  }

  private static long maxUnsigned(
    final long x,
    final long y)
  {
    if (Long.compareUnsigned(x, y) > 0) {
      return x;
    }
    return y;
  }

  @Override
  public int read(
    final ByteBuffer dst)
  {
    throw new NonReadableChannelException();
  }

  @Override
  public int write(
    final ByteBuffer src)
    throws IOException
  {
    final var wrote = this.delegate.write(src);
    this.uppermost = maxUnsigned(this.position(), this.uppermost);
    return wrote;
  }

  @Override
  public long position()
    throws IOException
  {
    return this.delegate.position() - this.baseStart;
  }

  @Override
  public SeekableByteChannel position(
    final long newPosition)
    throws IOException
  {
    this.uppermost = maxUnsigned(newPosition, this.uppermost);
    return this.delegate.position(this.baseStart + newPosition);
  }

  public long wroteAtMost()
  {
    return this.uppermost;
  }

  @Override
  public long size()
  {
    return this.limit;
  }

  @Override
  public SeekableByteChannel truncate(
    final long size)
  {
    throw new UnsupportedOperationException();
  }

  @Override
  public boolean isOpen()
  {
    return this.delegate.isOpen();
  }

  @Override
  public void close()
    throws IOException
  {
    this.onClose.execute(this);
  }
}
