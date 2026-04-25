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
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.quarrel.core.QStringType.QLocalize;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * The 'show-metadata' command.
 */

public final class CLNCommandShowMetadata extends CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandShowMetadata.class);

  /**
   * The 'show-metadata' command.
   */

  public CLNCommandShowMetadata()
  {
    super(
      new QCommandMetadata(
        "show-metadata",
        new QConstant("Display texture file metadata."),
        Optional.of(new QLocalize("cmd.show-metadata.helpExt"))
      )
    );
  }

  @Override
  protected List<QParameterNamedType<?>>
  onListNamedParametersWithFile()
  {
    return List.of();
  }

  @Override
  protected QCommandStatus executeWithReadFile(
    final QCommandContextType context,
    final CLNFileReadableType fileParsed)
    throws IOException
  {
    final var sectionMetadata =
      fileParsed.openMetadata();

    if (sectionMetadata.isEmpty()) {
      LOG.error("No metadata section is present");
      return QCommandStatus.FAILURE;
    }

    try (var section = sectionMetadata.orElseThrow()) {
      final var metadata = section.metadata();
      final var keys = new ArrayList<String>(metadata.size());
      keys.addAll(metadata.keySet());
      keys.sort(String::compareTo);
      for (final var key : keys) {
        final var val = metadata.get(key);
        context.output().printf("%s: %s%n", key, val);
      }
      context.output().flush();
    }

    return QCommandStatus.SUCCESS;
  }
}
