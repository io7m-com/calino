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

package com.io7m.calino.parser.api;

import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.api.CLNVersion;

import java.io.IOException;
import java.net.URI;
import java.nio.ByteBuffer;
import java.nio.channels.SeekableByteChannel;
import java.util.Objects;

import static java.nio.ByteOrder.BIG_ENDIAN;

/**
 * The default version probe factory.
 */

public final class CLNProbes implements CLNProbeFactoryType
{
  /**
   * The default version probe factory.
   */

  public CLNProbes()
  {

  }

  @Override
  public CLNProbeType createProbe(
    final URI source,
    final SeekableByteChannel channel)
  {
    return new CLNProbe(source, channel);
  }

  @Override
  public String toString()
  {
    return String.format(
      "[%s 0x%s]",
      this.getClass().getSimpleName(),
      Integer.toUnsignedString(this.hashCode(), 16)
    );
  }

  private static final class CLNProbe implements CLNProbeType
  {
    private final URI source;
    private final SeekableByteChannel channel;

    private CLNProbe(
      final URI inSource,
      final SeekableByteChannel inChannel)
    {
      this.source =
        Objects.requireNonNull(inSource, "source");
      this.channel =
        Objects.requireNonNull(inChannel, "channel");
    }

    @Override
    public String toString()
    {
      return String.format(
        "[%s 0x%s]",
        this.getClass().getSimpleName(),
        Integer.toUnsignedString(this.hashCode(), 16)
      );
    }

    @Override
    public CLNVersion execute()
      throws IOException
    {
      final var buffer = ByteBuffer.allocate(8);
      buffer.order(BIG_ENDIAN);

      this.channel.position(0L);

      buffer.rewind();
      buffer.limit(8);
      {
        final var r = this.channel.read(buffer);
        if (r != 8) {
          throw new IOException(
            this.errorShortRead(this.channel.position(), r, 8));
        }
      }

      final var identifier = buffer.getLong(0);
      if (identifier != CLNIdentifiers.fileIdentifier()) {
        throw new IOException(
          this.errorMagicNumber(identifier));
      }

      buffer.rewind();
      buffer.limit(4);
      {
        final var r = this.channel.read(buffer);
        if (r != 4) {
          throw new IOException(
            this.errorShortRead(this.channel.position(), r, 4));
        }
      }

      final var major = buffer.getInt(0);
      buffer.rewind();
      buffer.limit(4);
      final var r = this.channel.read(buffer);
      {
        if (r != 4) {
          throw new IOException(
            this.errorShortRead(this.channel.position(), r, 4));
        }
      }

      final var minor = buffer.getInt(0);
      return new CLNVersion(major, minor);
    }

    private String errorShortRead(
      final long position,
      final int octets,
      final int expected)
    {
      final var lineSeparator = System.lineSeparator();
      return new StringBuilder(64)
        .append("File is truncated.")
        .append(lineSeparator)
        .append("  File: ")
        .append(this.source)
        .append(lineSeparator)
        .append("  At offset 0x")
        .append(Long.toUnsignedString(position, 16))
        .append(" we expected to read ")
        .append(Integer.toUnsignedString(expected))
        .append(" but only received ")
        .append(octets)
        .append(lineSeparator)
        .toString();
    }

    private String errorMagicNumber(
      final long identifier)
    {
      final var lineSeparator = System.lineSeparator();
      return new StringBuilder(64)
        .append("Unrecognized file identifier.")
        .append(lineSeparator)
        .append("  File: ")
        .append(this.source)
        .append(lineSeparator)
        .append("  Received: 0x")
        .append(Long.toUnsignedString(identifier, 16))
        .append(lineSeparator)
        .append("  Expected: 0x")
        .append(Long.toUnsignedString(CLNIdentifiers.fileIdentifier(), 16))
        .append(lineSeparator)
        .toString();
    }
  }
}
