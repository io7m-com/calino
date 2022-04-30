/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

package com.io7m.calino.vanilla;

import com.io7m.calino.validation.api.CLNValidationRequest;
import com.io7m.calino.validation.api.CLNValidatorFactoryType;
import com.io7m.calino.validation.api.CLNValidatorType;
import com.io7m.calino.vanilla.internal.CLN1ValidationErrors;
import com.io7m.calino.vanilla.internal.CLN1ValidationStrings;
import com.io7m.calino.vanilla.internal.CLN1Validator;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.Locale;
import java.util.Objects;

/**
 * A factory of version 1 validators.
 */

public final class CLN1Validators implements CLNValidatorFactoryType
{
  private final CLN1ValidationStrings strings;

  /**
   * A factory of version 1 validators.
   */

  public CLN1Validators()
  {
    this(Locale.getDefault());
  }

  /**
   * A factory of version 1 validators.
   *
   * @param locale The locale for error messages
   */

  public CLN1Validators(
    final Locale locale)
  {
    try {
      this.strings = new CLN1ValidationStrings(locale);
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  @Override
  public int supportedMajorVersion()
  {
    return 1;
  }

  @Override
  public int highestMinorVersion()
  {
    return 0;
  }

  @Override
  public CLNValidatorType createValidator(
    final CLNValidationRequest request)
  {
    Objects.requireNonNull(request, "request");
    return new CLN1Validator(
      new CLN1ValidationErrors(request.source(), this.strings),
      request.file()
    );
  }
}
