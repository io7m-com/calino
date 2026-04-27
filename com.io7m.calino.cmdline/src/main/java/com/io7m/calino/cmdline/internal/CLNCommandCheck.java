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

import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.validation.api.CLNValidationError;
import com.io7m.calino.validation.api.CLNValidationRequest;
import com.io7m.calino.validation.api.CLNValidators;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.quarrel.core.QStringType.QLocalize;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.List;
import java.util.Optional;

import static com.io7m.calino.validation.api.CLNValidationStatus.STATUS_ERROR;
import static com.io7m.calino.validation.api.CLNValidationStatus.STATUS_WARNING;
import static java.lang.Boolean.FALSE;

/**
 * The 'check' command.
 */

public final class CLNCommandCheck extends CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandCheck.class);

  private static final QParameterNamed1<Boolean> WARNINGS_AS_ERRORS =
    new QParameterNamed1<>(
      "--warnings-as-errors",
      List.of(),
      new QConstant("Treat validation warnings as errors."),
      Optional.of(FALSE),
      Boolean.class
    );

  private static final QParameterNamed1<CLNVersion> FORMAT_VERSION =
    new QParameterNamed1<>(
      "--format-version",
      List.of(),
      new QConstant("The requested file format version."),
      Optional.of(new CLNVersion(1, 0)),
      CLNVersion.class
    );

  /**
   * The 'check' command.
   */

  public CLNCommandCheck()
  {
    super(
      new QCommandMetadata(
        "check",
        new QConstant("Validate a texture file."),
        Optional.of(new QLocalize("cmd.check.helpExt"))
      )
    );
  }

  private static void quoteSpec(
    final CLNValidationError e)
  {
    e.specificationSectionId().ifPresent(id -> {
      switch (e.status()) {
        case STATUS_WARNING -> {
          LOG.warn(
            "  See https://www.io7m.com/software/calino/specification/index.xhtml#id_{} for details.",
            id);
        }
        case STATUS_ERROR -> {
          LOG.error(
            "  See https://www.io7m.com/software/calino/specification/index.xhtml#id_{} for details.",
            id);
        }
      }
    });
  }

  @Override
  protected List<QParameterNamedType<?>>
  onListNamedParametersWithFile()
  {
    return List.of(
      FORMAT_VERSION,
      WARNINGS_AS_ERRORS
    );
  }

  @Override
  protected QCommandStatus executeWithReadFile(
    final QCommandContextType context,
    final CLNFileReadableType fileParsed)
    throws IOException
  {
    final var validators = new CLNValidators();

    final var formatVersion =
      context.parameterValue(FORMAT_VERSION);
    final var warningsAsErrors =
      context.parameterValue(WARNINGS_AS_ERRORS);

    final var validatorFactoryOpt =
      validators.findValidatorFactoryFor(formatVersion);

    if (validatorFactoryOpt.isEmpty()) {
      LOG.error(
        "No available validators for format version {}",
        formatVersion);
      return QCommandStatus.FAILURE;
    }

    final var request =
      new CLNValidationRequest(fileParsed, source(context));

    final var validator =
      validatorFactoryOpt.get()
        .createValidator(request);

    final var errors =
      validator.execute();

    final var allErrors =
      errors.stream()
        .filter(e -> e.status() == STATUS_ERROR)
        .toList();

    final var allWarnings =
      errors.stream()
        .filter(e -> e.status() == STATUS_WARNING)
        .toList();

    for (final var e : allErrors) {
      LOG.error(
        "{}: @0x{}: {}",
        e.source(),
        Long.toUnsignedString(e.offset(), 16),
        e.message()
      );
      quoteSpec(e);
    }

    for (final var e : allWarnings) {
      LOG.warn(
        "{}: @0x{}: {}",
        e.source(),
        Long.toUnsignedString(e.offset(), 16),
        e.message()
      );
      quoteSpec(e);
    }

    if (!allErrors.isEmpty()) {
      return QCommandStatus.FAILURE;
    }

    if (warningsAsErrors.booleanValue()) {
      if (!allWarnings.isEmpty()) {
        LOG.info("treating warnings as errors");
        return QCommandStatus.FAILURE;
      }
    }

    return QCommandStatus.SUCCESS;
  }
}
