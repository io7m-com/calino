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

package com.io7m.calino.api;

/**
 * A compression method. This refers to compression that is used on data that
 * will be uploaded directly to a GPU without prior decompression. This is in
 * contrast to <i>supercompression</i> which is used to encapsulate data that
 * must be decompressed before it can be used.
 *
 * @see CLNSuperCompressionMethodType
 */

public sealed interface CLNCompressionMethodType extends CLNDescribableType
  permits CLNCompressionMethodCustom, CLNCompressionMethodStandard
{
  /**
   * @return The identifier of the section containing data required to
   * decompress data
   */

  long compressionSectionIdentifier();

  /**
   * @return The size of a compressed block on the X axis
   */

  int blockSizeX();

  /**
   * @return The size of a compressed block on the Y axis
   */

  int blockSizeY();

  /**
   * @return The required alignment of a compressed block
   */

  int blockAlignment();
}
