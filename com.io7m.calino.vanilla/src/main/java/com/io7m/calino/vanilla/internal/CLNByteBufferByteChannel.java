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
import java.nio.channels.ClosedChannelException;
import java.nio.channels.SeekableByteChannel;
import java.util.Objects;

import static java.lang.Integer.toUnsignedLong;

/**
 * A seekable byte channel based on an underlying byte buffer.
 */

public final class CLNByteBufferByteChannel implements SeekableByteChannel
{
  private final ByteBuffer buffer;
  private boolean closed;
  private long position;

  /**
   * A seekable byte channel based on an underlying byte buffer.
   *
   * @param inBuffer The byte buffer
   */

  public CLNByteBufferByteChannel(
    final ByteBuffer inBuffer)
  {
    this.buffer =
      Objects.requireNonNull(inBuffer, "buffer");
    this.closed =
      false;
  }

  private static long minUnsigned(
    final long x,
    final long y)
  {
    if (Long.compareUnsigned(x, y) < 0) {
      return x;
    }
    return y;
  }

  private long remaining()
  {
    return toUnsignedLong(this.buffer.capacity()) - this.position;
  }

  @Override
  public int read(
    final ByteBuffer dst)
    throws IOException
  {
    this.checkOpen();

    final var remaining =
      minUnsigned(this.remaining(), toUnsignedLong(dst.remaining()));
    final var slice =
      this.buffer.slice(Math.toIntExact(this.position), (int) remaining);

    dst.put(slice);
    this.position += remaining;
    return (int) remaining;
  }

  private void checkOpen()
    throws ClosedChannelException
  {
    if (this.closed) {
      throw new ClosedChannelException();
    }
  }

  @Override
  public int write(
    final ByteBuffer src)
    throws IOException
  {
    this.checkOpen();

    final var remaining =
      minUnsigned(this.remaining(), toUnsignedLong(src.remaining()));
    final var slice =
      src.slice(src.position(), (int) remaining);

    this.buffer.put(slice);
    this.position += remaining;
    return (int) remaining;
  }

  @Override
  public long position()
    throws IOException
  {
    this.checkOpen();
    return this.position;
  }

  @Override
  public SeekableByteChannel position(
    final long newPosition)
  {
    this.position = newPosition;
    return this;
  }

  @Override
  public long size()
    throws IOException
  {
    this.checkOpen();
    return toUnsignedLong(this.buffer.capacity());
  }

  @Override
  public SeekableByteChannel truncate(
    final long size)
    throws IOException
  {
    this.checkOpen();
    return this;
  }

  @Override
  public boolean isOpen()
  {
    return !this.closed;
  }

  @Override
  public void close()
    throws IOException
  {
    this.closed = true;
  }
}
