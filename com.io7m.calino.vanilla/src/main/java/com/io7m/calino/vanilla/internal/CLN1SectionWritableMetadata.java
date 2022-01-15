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

package com.io7m.calino.vanilla.internal;

import com.io7m.calino.api.CLNSectionWritableMetadataType;
import com.io7m.calino.api.CLNSectionWritableType;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;

import java.io.IOException;
import java.util.Map;
import java.util.Objects;

import static java.lang.Integer.toUnsignedLong;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A writable metadata section.
 */

public final class CLN1SectionWritableMetadata
  extends CLN1SectionWritableAbstract
  implements CLNSectionWritableMetadataType
{
  private final BSSWriterProviderType writers;

  /**
   * A writable metadata section.
   *
   * @param inWriters    A writer provider
   * @param inOnClose    A function executed on closing
   * @param inRequest    A write request
   * @param inIdentifier An identifier
   * @param inWriter     A writer
   */

  public CLN1SectionWritableMetadata(
    final BSSWriterProviderType inWriters,
    final BSSWriterRandomAccessType inWriter,
    final CLNWriteRequest inRequest,
    final long inIdentifier,
    final CLNOnCloseOperationType<CLNSectionWritableType> inOnClose)
  {
    super(inWriter, inRequest, inIdentifier, inOnClose);
    this.writers = Objects.requireNonNull(inWriters, "inWriters");
  }

  @Override
  public void setMetadata(
    final Map<String, String> metadata)
    throws IOException
  {
    Objects.requireNonNull(metadata, "metadata");

    try (var channel = this.sectionDataChannel()) {
      final var targetURI = this.request().target();
      try (var writer =
             this.writers.createWriterFromChannel(
               targetURI, channel, "metadata")) {
        writer.writeU32BE(toUnsignedLong(metadata.size()));

        for (final var entry : metadata.entrySet()) {
          final var key = entry.getKey();
          final var val = entry.getValue();
          final var keyBytes = key.getBytes(UTF_8);
          final var valBytes = val.getBytes(UTF_8);

          writer.writeU32BE(toUnsignedLong(keyBytes.length));
          writer.writeBytes(keyBytes);
          writer.align(4);
          writer.writeU32BE(toUnsignedLong(valBytes.length));
          writer.writeBytes(valBytes);
          writer.align(4);
        }
      }
    }
  }
}
