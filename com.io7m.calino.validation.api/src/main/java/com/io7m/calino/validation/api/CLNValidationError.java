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

package com.io7m.calino.validation.api;

import java.net.URI;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

/**
 * An error produced during validation.
 *
 * @param source                 The source file
 * @param offset                 The octet offset of the error
 * @param status                 The error status
 * @param specificationSectionId The UUID of the specification section
 *                               describing the error, if any
 * @param message                The error message
 * @param exception              The exception, if any
 */

public record CLNValidationError(
  URI source,
  long offset,
  CLNValidationStatus status,
  Optional<UUID> specificationSectionId,
  String message,
  Optional<Exception> exception)
{
  /**
   * An error produced during validation.
   *
   * @param source                 The source file
   * @param offset                 The octet offset of the error
   * @param status                 The error status
   * @param specificationSectionId The UUID of the specification section
   *                               describing the error, if any
   * @param message                The error message
   * @param exception              The exception, if any
   */

  public CLNValidationError
  {
    Objects.requireNonNull(source, "source");
    Objects.requireNonNull(status, "status");
    Objects.requireNonNull(specificationSectionId, "specificationSectionId");
    Objects.requireNonNull(message, "message");
    Objects.requireNonNull(exception, "exception");
  }
}
