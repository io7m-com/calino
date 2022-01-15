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

import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNSectionReadableMetadataType;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A readable metadata section.
 */

public final class CLN1SectionReadableMetadata
  extends CLN1SectionReadableAbstract implements CLNSectionReadableMetadataType
{
  /**
   * A readable metadata section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  CLN1SectionReadableMetadata(
    final BSSReaderRandomAccessType inReader,
    final CLNParseRequest inRequest,
    final CLNFileSectionDescription inDescription)
  {
    super(inReader, inRequest, inDescription);
  }

  private static String makeString(
    final byte[] data)
  {
    // CHECKSTYLE:OFF
    return new String(data, UTF_8);
    // CHECKSTYLE:ON
  }

  @Override
  public Map<String, String> metadata()
    throws IOException
  {
    final var reader =
      this.reader();
    final var fileOffset =
      this.fileSectionDescription().fileOffset();
    final var sectionSize =
      this.description().size();

    reader.seekTo(fileOffset);
    reader.skip(16L);

    final var metadata = new HashMap<String, String>();
    try (var subReader =
           reader.createSubReaderAtBounded(
             "metadata", 0L, sectionSize)) {

      if (subReader.bytesRemaining().orElse(0L) == 0L) {
        return Map.of();
      }

      final int count =
        (int) (subReader.readU32BE("count") & 0xffff_ffffL);

      for (int index = 0; index < count; ++index) {
        final var keyLength =
          subReader.readU32BE("keyLength");

        final var limit = this.request().keyValueDatumLimit();
        if (Long.compareUnsigned(keyLength, limit) > 0) {
          throw new IOException(
            this.errorLimitExceeded(
              keyLength, limit, "key/value datum limit"));
        }

        final var keyData = new byte[(int) keyLength];
        subReader.readBytes(keyData);
        subReader.align(4);

        final var valLength =
          subReader.readU32BE("valLength");

        if (Long.compareUnsigned(valLength, limit) > 0) {
          throw new IOException(
            this.errorLimitExceeded(
              valLength, limit, "key/value datum limit"));
        }

        final var valData = new byte[(int) valLength];
        subReader.readBytes(valData);
        subReader.align(4);

        final var key = makeString(keyData);
        final var val = makeString(valData);
        metadata.put(key, val);
      }
    }
    return Map.copyOf(metadata);
  }
}
