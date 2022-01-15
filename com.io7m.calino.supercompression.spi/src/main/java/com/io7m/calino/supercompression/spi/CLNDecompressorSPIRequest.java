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

package com.io7m.calino.supercompression.spi;

import com.io7m.calino.api.CLNImageDescriptionType;
import com.io7m.calino.api.CLNSuperCompressionMethodType;

import java.nio.channels.SeekableByteChannel;
import java.util.Objects;

/**
 * A request to decompress data.
 *
 * @param method           The compression method
 * @param imageDescription The image description
 * @param channel          A channel containing compressed data
 */

public record CLNDecompressorSPIRequest(
  CLNSuperCompressionMethodType method,
  CLNImageDescriptionType imageDescription,
  SeekableByteChannel channel)
{
  /**
   * A request to decompress data.
   *
   * @param method           The compression method
   * @param imageDescription The image description
   * @param channel          A channel containing compressed data
   */

  public CLNDecompressorSPIRequest
  {
    Objects.requireNonNull(method, "method");
    Objects.requireNonNull(imageDescription, "imageDescription");
    Objects.requireNonNull(channel, "channel");
  }
}
