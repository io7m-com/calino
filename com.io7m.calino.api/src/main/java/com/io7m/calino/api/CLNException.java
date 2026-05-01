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

package com.io7m.calino.api;

import com.io7m.seltzer.api.SStructuredErrorExceptionType;
import com.io7m.seltzer.api.SStructuredErrorType;

import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeoutException;

/**
 * The base type of exceptions raised by the package.
 */

public final class CLNException
  extends Exception
  implements SStructuredErrorExceptionType<String>
{
  private final Map<String, String> attributes;
  private final String errorCode;
  private final Optional<String> remediatingAction;

  /**
   * Construct an exception.
   *
   * @param message             The message
   * @param inAttributes        The attributes
   * @param inErrorCode         The error code
   * @param inRemediatingAction The remediating action
   */

  public CLNException(
    final String message,
    final Map<String, String> inAttributes,
    final String inErrorCode,
    final Optional<String> inRemediatingAction)
  {
    super(Objects.requireNonNull(message, "message"));

    this.attributes =
      Map.copyOf(inAttributes);
    this.errorCode =
      Objects.requireNonNull(inErrorCode, "errorCode");
    this.remediatingAction =
      Objects.requireNonNull(inRemediatingAction, "remediatingAction");
  }

  /**
   * Construct an exception.
   *
   * @param message             The message
   * @param cause               The cause
   * @param inAttributes        The attributes
   * @param inErrorCode         The error code
   * @param inRemediatingAction The remediating action
   */

  public CLNException(
    final String message,
    final Throwable cause,
    final Map<String, String> inAttributes,
    final String inErrorCode,
    final Optional<String> inRemediatingAction)
  {
    super(
      Objects.requireNonNull(message, "message"),
      Objects.requireNonNull(cause, "cause")
    );

    this.attributes =
      Map.copyOf(inAttributes);
    this.errorCode =
      Objects.requireNonNull(inErrorCode, "errorCode");
    this.remediatingAction =
      Objects.requireNonNull(inRemediatingAction, "remediatingAction");
  }

  /**
   * Construct an exception.
   *
   * @param cause               The cause
   * @param inAttributes        The attributes
   * @param inErrorCode         The error code
   * @param inRemediatingAction The remediating action
   */

  public CLNException(
    final Throwable cause,
    final Map<String, String> inAttributes,
    final String inErrorCode,
    final Optional<String> inRemediatingAction)
  {
    super(Objects.requireNonNull(cause, "cause"));

    this.attributes =
      Map.copyOf(inAttributes);
    this.errorCode =
      Objects.requireNonNull(inErrorCode, "errorCode");
    this.remediatingAction =
      Objects.requireNonNull(inRemediatingAction, "remediatingAction");
  }

  /**
   * Wrap the given exception. The function takes into account whether the
   * incoming exception is a structured error, and the existing exception
   * might be treated as the cause of the wrapped exception.
   *
   * @param x The exception
   *
   * @return The wrapped result
   */

  public static CLNException wrap(
    final Throwable x)
  {
    return switch (x) {
      case final CLNException e -> e;

      case final SStructuredErrorType<?> e -> {
        yield new CLNException(
          e.message(),
          x,
          e.attributes(),
          e.errorCode().toString(),
          e.remediatingAction()
        );
      }

      case final TimeoutException e -> {
        yield new CLNException(
          Objects.requireNonNullElse(x.getMessage(), x.getClass().getName()),
          x,
          Map.of(),
          "error-timeout",
          Optional.empty()
        );
      }

      case final InterruptedException e -> {
        yield new CLNException(
          Objects.requireNonNullElse(x.getMessage(), x.getClass().getName()),
          x,
          Map.of(),
          "error-interrupted",
          Optional.empty()
        );
      }

      case final ExecutionException e -> {
        yield wrap(e.getCause());
      }

      default -> {
        yield new CLNException(
          Objects.requireNonNullElse(x.getMessage(), x.getClass().getName()),
          x,
          Map.of(),
          "error-exception",
          Optional.empty()
        );
      }
    };
  }

  @Override
  public Map<String, String> attributes()
  {
    return this.attributes;
  }

  @Override
  public String errorCode()
  {
    return this.errorCode;
  }

  @Override
  public Optional<String> remediatingAction()
  {
    return this.remediatingAction;
  }

  @Override
  public Optional<Throwable> exception()
  {
    return Optional.of(this);
  }
}
