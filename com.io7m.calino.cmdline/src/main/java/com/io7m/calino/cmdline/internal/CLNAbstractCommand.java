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

import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandType;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.ext.logback.QLogback;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Objects;

/**
 * An abstract calino command.
 */

public abstract class CLNAbstractCommand implements QCommandType
{
  private final CLNStrings calinoStrings;
  private final QCommandMetadata metadata;

  CLNAbstractCommand(
    final QCommandMetadata inMetadata)
  {
    this.metadata =
      Objects.requireNonNull(inMetadata, "Metadata");

    try {
      this.calinoStrings = new CLNStrings(Locale.getDefault());
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  protected abstract List<QParameterNamedType<?>> onListNamedParametersActual();

  @Override
  public final List<QParameterNamedType<?>> onListNamedParameters()
  {
    final var parameters = new ArrayList<QParameterNamedType<?>>(16);
    parameters.addAll(QLogback.parameters());
    parameters.addAll(this.onListNamedParametersActual());
    return List.copyOf(parameters);
  }

  @Override
  public final QCommandMetadata metadata()
  {
    return this.metadata;
  }

  /**
   * @return The string resources
   */

  public final CLNStrings calinoStrings()
  {
    return this.calinoStrings;
  }
}
