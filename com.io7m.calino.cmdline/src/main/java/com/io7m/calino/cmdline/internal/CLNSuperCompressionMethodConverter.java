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

package com.io7m.calino.cmdline.internal;

import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.quarrel.core.QException;
import com.io7m.quarrel.core.QValueConverterType;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * A value converter.
 */

public final class CLNSuperCompressionMethodConverter
  implements QValueConverterType<CLNSuperCompressionMethodType>
{
  /**
   * A value converter.
   */

  public CLNSuperCompressionMethodConverter()
  {

  }

  @Override
  public CLNSuperCompressionMethodType convertFromString(
    final String text)
    throws QException
  {
    try {
      return CLNSuperCompressionMethodType.parse(text, 0L);
    } catch (final Exception e) {
      throw new QException(
        Objects.requireNonNullElse(e.getMessage(), e.getClass().getName()),
        "error-exception",
        Map.of("Input", text),
        Optional.empty(),
        List.of()
      );
    }
  }

  @Override
  public String convertToString(
    final CLNSuperCompressionMethodType value)
  {
    return value.descriptor();
  }

  @Override
  public CLNSuperCompressionMethodType exampleValue()
  {
    return CLNSuperCompressionMethodStandard.LZ4;
  }

  @Override
  public String syntax()
  {
    return "<descriptor-string>";
  }

  @Override
  public Class<CLNSuperCompressionMethodType> convertedClass()
  {
    return CLNSuperCompressionMethodType.class;
  }
}
