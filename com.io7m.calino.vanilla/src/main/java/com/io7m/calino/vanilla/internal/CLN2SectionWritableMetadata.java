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

import com.io7m.calino.api.CLNException;
import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.api.CLNSectionWritableMetadataType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.seltzer.io.SIOException;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static java.lang.Integer.toUnsignedLong;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A writable image info section.
 */

final class CLN2SectionWritableMetadata
  extends CLN2SectionWritableAbstract
  implements CLNSectionWritableMetadataType
{
  CLN2SectionWritableMetadata(
    final CloseableCollectionType<CLNException> resources,
    final CLNOnCloseOperationType<CLN2SectionWritableAbstract> inOnClose)
    throws IOException
  {
    super(CLNIdentifiers.sectionMetadataIdentifier(), resources, inOnClose);
  }

  @Override
  public void setMetadata(
    final Map<String, List<String>> metadata)
    throws IOException
  {
    final var writer = this.writer();
    writer.writeU32BE(toUnsignedLong(metadata.size()));

    final var sortedMap = new TreeMap<>(metadata);
    for (final var entry : sortedMap.entrySet()) {
      final var key = entry.getKey();
      final var values = entry.getValue();
      for (final var value : values) {
        writeStringAligned(writer, key);
        writeStringAligned(writer, value);
      }
    }
  }

  private static void writeStringAligned(
    final BSSWriterRandomAccessType writer,
    final String text)
    throws SIOException
  {
    final var bytes = text.getBytes(UTF_8);
    writer.writeU32BE(toUnsignedLong(bytes.length));
    writer.writeBytes(bytes);
    final var positionThen = writer.offsetCurrentRelative();
    writer.align(4);
    final var positionNow = writer.offsetCurrentRelative();
    if (positionNow != positionThen) {
      writer.seekTo(positionNow - 1L);
      writer.writeU8(0);
    }
  }
}
