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

package com.io7m.calino.cmdline.internal;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.validation.api.CLNValidationRequest;
import com.io7m.calino.validation.api.CLNValidators;
import com.io7m.claypot.core.CLPCommandContextType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.stream.Collectors;

import static com.io7m.calino.validation.api.CLNValidationStatus.STATUS_ERROR;
import static com.io7m.calino.validation.api.CLNValidationStatus.STATUS_WARNING;
import static com.io7m.claypot.core.CLPCommandType.Status.FAILURE;
import static com.io7m.claypot.core.CLPCommandType.Status.SUCCESS;

/**
 * The 'check' command.
 */

@Parameters(commandDescription = "Check a texture file.")
public final class CLNCommandCheck extends CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandCheck.class);

  @Parameter(
    description = "Treat validation warnings as errors",
    arity = 1,
    required = false,
    names = "--warnings-as-errors")
  private boolean warningsAsErrors;

  @Parameter(
    required = false,
    description = "The requested file format version",
    converter = CLNVersionStringConverter.class,
    names = "--format-version")
  private CLNVersion formatVersion = new CLNVersion(1, 0);

  /**
   * The 'check' command.
   *
   * @param inContext The context
   */

  public CLNCommandCheck(
    final CLPCommandContextType inContext)
  {
    super(inContext);
  }

  @Override
  public String extendedHelp()
  {
    return this.calinoStrings().format("cmd.check.helpExt");
  }

  @Override
  protected Status executeWithReadFile(
    final CLNFileReadableType fileParsed)
  {
    final var validators = new CLNValidators();

    final var validatorFactoryOpt =
      validators.findValidatorFactoryFor(this.formatVersion);

    if (validatorFactoryOpt.isEmpty()) {
      LOG.error(
        "no available validators for format version {}",
        this.formatVersion);
      return FAILURE;
    }

    final var request =
      new CLNValidationRequest(fileParsed, this.source());

    final var validator =
      validatorFactoryOpt.get()
        .createValidator(request);

    final var errors =
      validator.execute();

    final var allErrors =
      errors.stream()
        .filter(e -> e.status() == STATUS_ERROR)
        .collect(Collectors.toList());

    final var allWarnings =
      errors.stream()
        .filter(e -> e.status() == STATUS_WARNING)
        .collect(Collectors.toList());

    allErrors.addAll(this.parserValidationErrors());
    allWarnings.addAll(this.parserValidationWarnings());

    for (final var e : allErrors) {
      LOG.error(
        "{}: @0x{}: {}",
        e.source(),
        Long.toUnsignedString(e.offset(), 16),
        e.message()
      );
    }

    for (final var e : allWarnings) {
      LOG.warn(
        "{}: @0x{}: {}",
        e.source(),
        Long.toUnsignedString(e.offset(), 16),
        e.message()
      );
    }

    if (!allErrors.isEmpty()) {
      return FAILURE;
    }

    if (this.warningsAsErrors) {
      if (!allWarnings.isEmpty()) {
        LOG.info("treating warnings as errors");
        return FAILURE;
      }
    }

    return SUCCESS;
  }

  @Override
  public String name()
  {
    return "check";
  }
}
