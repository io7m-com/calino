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

import java.util.List;
import java.util.Optional;

/**
 * The 'show-sections' command.
 */

public final class CLNCommandShowSections extends CLNAbstractReadFileCommand
{
  /**
   * The 'show-sections' command.
   */

  public CLNCommandShowSections()
  {
    super(
      new QCommandMetadata(
        "show-sections",
        new QConstant("List sections in a texture file."),
        Optional.of(new QLocalize("cmd.show-sections.helpExt"))
      )
    );
  }

  @Override
  protected List<QParameterNamedType<?>> onListNamedParametersWithFile()
  {
    return List.of();
  }

  @Override
  protected QCommandStatus executeWithReadFile(
    final QCommandContextType context,
    final CLNFileReadableType fileParsed)
  {
    final var sections = fileParsed.sections();
    for (int index = 0; index < sections.size(); ++index) {
      final var fileSection = sections.get(index);
      context.output().printf(
        "%s %s%n",
        Integer.toUnsignedString(index),
        fileSection.show()
      );
    }
    return QCommandStatus.SUCCESS;
  }
}
