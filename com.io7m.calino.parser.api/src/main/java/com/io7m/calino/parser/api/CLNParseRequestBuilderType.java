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

import java.net.URI;
import java.nio.channels.SeekableByteChannel;

/**
 * A mutable parser request builder.
 *
 * @see CLNParseRequest
 */

public interface CLNParseRequestBuilderType
{
  /**
   * @return The file channel
   */

  SeekableByteChannel channel();

  /**
   * Set the file channel.
   *
   * @param inChannel The channel
   *
   * @return this
   */

  CLNParseRequestBuilderType setChannel(
    SeekableByteChannel inChannel);

  /**
   * @return The file source
   */

  URI source();

  /**
   * Set the file source.
   *
   * @param inSource The source
   *
   * @return this
   */

  CLNParseRequestBuilderType setSource(
    URI inSource);

  /**
   * @return The descriptor length limit
   */

  long descriptorLengthLimit();

  /**
   * Set the descriptor length limit.
   *
   * @param limit The limit
   *
   * @return this
   */

  CLNParseRequestBuilderType setDescriptorLengthLimit(
    long limit);

  /**
   * @return The maximum length of a key or value in metadata
   */

  long keyValueDatumLimit();

  /**
   * Set the maximum length of a key or value in metadata.
   *
   * @param limit The limit
   *
   * @return this
   */

  CLNParseRequestBuilderType setKeyValueDatumLimit(
    long limit);

  /**
   * @return An immutable parse request
   */

  CLNParseRequest build();
}
