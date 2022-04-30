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

import com.io7m.calino.supercompression.api.CLNDecompressorFactoryType;

import java.net.URI;
import java.nio.channels.SeekableByteChannel;
import java.util.Objects;

/**
 * A parse request.
 *
 * @param decompressors         The decompressor factory
 * @param channel               The file channel
 * @param source                The data source
 * @param descriptorLengthLimit The maximum descriptor length
 * @param keyValueDatumLimit    The maximum value of a metadata key or value
 */

public final record CLNParseRequest(
  CLNDecompressorFactoryType decompressors,
  SeekableByteChannel channel,
  URI source,
  long descriptorLengthLimit,
  long keyValueDatumLimit)
{
  /**
   * A parse request.
   *
   * @param decompressors         The decompressor factory
   * @param channel               The file channel
   * @param source                The data source
   * @param descriptorLengthLimit The maximum descriptor length
   * @param keyValueDatumLimit    The maximum value of a metadata key or value
   */

  public CLNParseRequest
  {
    Objects.requireNonNull(decompressors, "decompressors");
    Objects.requireNonNull(channel, "channel");
    Objects.requireNonNull(source, "source");
  }

  /**
   * Create a new mutable request builder.
   *
   * @param inDecompressors The decompressor factory
   * @param inChannel       The file channel
   * @param inSource        The data source
   *
   * @return A request builder
   */

  public static CLNParseRequestBuilderType builder(
    final CLNDecompressorFactoryType inDecompressors,
    final SeekableByteChannel inChannel,
    final URI inSource)
  {
    return new Builder(inDecompressors, inChannel, inSource);
  }

  private static final class Builder
    implements CLNParseRequestBuilderType
  {
    private final CLNDecompressorFactoryType decompressors;
    private SeekableByteChannel channel;
    private URI source;
    private long keyValueDatumLimit = 1_000_000L;
    private long descriptorLengthLimit = 256L;

    private Builder(
      final CLNDecompressorFactoryType inDecompressors,
      final SeekableByteChannel inChannel,
      final URI inSource)
    {
      this.decompressors =
        Objects.requireNonNull(inDecompressors, "decompressors");
      this.channel =
        Objects.requireNonNull(inChannel, "channel");
      this.source =
        Objects.requireNonNull(inSource, "source");
    }

    @Override
    public SeekableByteChannel channel()
    {
      return this.channel;
    }

    @Override
    public CLNParseRequestBuilderType setChannel(
      final SeekableByteChannel inChannel)
    {
      this.channel = Objects.requireNonNull(inChannel, "channel");
      return this;
    }

    @Override
    public URI source()
    {
      return this.source;
    }

    @Override
    public CLNParseRequestBuilderType setSource(
      final URI inSource)
    {
      this.source = Objects.requireNonNull(inSource, "source");
      return this;
    }

    @Override
    public long descriptorLengthLimit()
    {
      return this.descriptorLengthLimit;
    }

    @Override
    public CLNParseRequestBuilderType setDescriptorLengthLimit(
      final long limit)
    {
      this.descriptorLengthLimit = limit;
      return this;
    }

    @Override
    public long keyValueDatumLimit()
    {
      return this.keyValueDatumLimit;
    }

    @Override
    public CLNParseRequestBuilderType setKeyValueDatumLimit(
      final long limit)
    {
      this.keyValueDatumLimit = limit;
      return this;
    }

    @Override
    public CLNParseRequest build()
    {
      return new CLNParseRequest(
        this.decompressors,
        this.channel,
        this.source,
        this.descriptorLengthLimit,
        this.keyValueDatumLimit
      );
    }
  }
}
