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

import com.io7m.calino.api.CLNException;
import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.api.CLNVersion;

import java.io.IOException;
import java.net.URI;
import java.nio.ByteBuffer;
import java.nio.channels.SeekableByteChannel;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

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
    private final HashMap<String, String> attributes;

    private CLNProbe(
      final URI inSource,
      final SeekableByteChannel inChannel)
    {
      this.source =
        Objects.requireNonNull(inSource, "source");
      this.channel =
        Objects.requireNonNull(inChannel, "channel");

      this.attributes = new HashMap<>();
      this.attributes.put("Source", this.source.toString());
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
      throws CLNException
    {
      try {
        final var buffer = ByteBuffer.allocate(8);
        buffer.order(BIG_ENDIAN);

        this.channel.position(0L);

        buffer.rewind();
        buffer.limit(8);
        {
          final var r = this.channel.read(buffer);
          if (r != 8) {
            throw this.errorShortRead(r, 8);
          }
        }

        final var identifier = buffer.getLong(0);
        if (identifier != CLNIdentifiers.fileIdentifier()) {
          throw this.errorMagicNumber(identifier);
        }

        buffer.rewind();
        buffer.limit(4);
        {
          final var r = this.channel.read(buffer);
          if (r != 4) {
            throw this.errorShortRead(r, 4);
          }
        }

        final var major = buffer.getInt(0);
        buffer.rewind();
        buffer.limit(4);
        final var r = this.channel.read(buffer);
        {
          if (r != 4) {
            throw this.errorShortRead(r, 4);
          }
        }

        final var minor = buffer.getInt(0);
        return new CLNVersion(major, minor);
      } catch (final Exception e) {
        throw CLNException.wrap(e);
      }
    }

    private CLNException errorShortRead(
      final int octets,
      final int expected)
      throws IOException
    {
      this.attributes.put(
        "Offset",
        "0x" + Long.toUnsignedString(this.channel.position(), 16)
      );
      this.attributes.put(
        "ReadExpected (Octets)",
        Integer.toUnsignedString(expected)
      );
      this.attributes.put(
        "ReadReceived (Octets)",
        Integer.toUnsignedString(octets)
      );

      return new CLNException(
        "File is truncated.",
        Map.copyOf(this.attributes),
        "error-file-truncated",
        Optional.empty()
      );
    }

    private CLNException errorMagicNumber(
      final long identifier)
      throws IOException
    {
      this.attributes.put(
        "Offset",
        "0x" + Long.toUnsignedString(this.channel.position(), 16)
      );
      this.attributes.put(
        "FileIdentifier (Expected)",
        Long.toUnsignedString(CLNIdentifiers.fileIdentifier(), 16)
      );
      this.attributes.put(
        "FileIdentifier (Received)",
        Long.toUnsignedString(identifier, 16)
      );

      return new CLNException(
        "File does not have the expected file identifier.",
        Map.copyOf(this.attributes),
        "error-file-identifier-incorrect",
        Optional.empty()
      );
    }
  }
}
