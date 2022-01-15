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

import com.beust.jcommander.Parameters;
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.claypot.core.CLPCommandContextType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.ArrayList;

import static com.io7m.claypot.core.CLPCommandType.Status.FAILURE;
import static com.io7m.claypot.core.CLPCommandType.Status.SUCCESS;

/**
 * The 'show-metadata' command.
 */

@Parameters(commandDescription = "Display texture file metadata.")
public final class CLNCommandShowMetadata extends CLNAbstractReadFileCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLNCommandShowMetadata.class);

  /**
   * The 'show-metadata' command.
   *
   * @param inContext The context
   */

  public CLNCommandShowMetadata(
    final CLPCommandContextType inContext)
  {
    super(inContext);
  }

  @Override
  public String extendedHelp()
  {
    return this.calinoStrings().format("cmd.show-metadata.helpExt");
  }

  @Override
  protected Status executeWithReadFile(
    final CLNFileReadableType fileParsed)
    throws IOException
  {
    final var sectionMetadata =
      fileParsed.openMetadata();

    if (sectionMetadata.isEmpty()) {
      LOG.error("no metadata section is present");
      return FAILURE;
    }

    try (var section = sectionMetadata.orElseThrow()) {
      final var metadata = section.metadata();
      final var keys = new ArrayList<String>(metadata.size());
      keys.addAll(metadata.keySet());
      keys.sort(String::compareTo);
      for (final var key : keys) {
        final var val = metadata.get(key);
        System.out.printf("%s: %s%n", key, val);
      }
      System.out.flush();
    }

    return SUCCESS;
  }

  @Override
  public String name()
  {
    return "show-metadata";
  }
}
