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

import com.io7m.calino.api.CLNSectionReadableMetadataType;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.entomos.core.EoFileSection;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A readable metadata section.
 */

public final class CLN2SectionReadableMetadata
  extends CLN2SectionReadableAbstract
  implements CLNSectionReadableMetadataType
{
  /**
   * A readable metadata section.
   *
   * @param inDescription The description
   * @param inReader      The reader
   * @param inRequest     The request
   */

  CLN2SectionReadableMetadata(
    final BSSReaderRandomAccessType inReader,
    final CLNParseRequest inRequest,
    final EoFileSection inDescription)
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
  public Map<String, List<String>> metadata()
    throws IOException
  {
    final var metadata = new HashMap<String, List<String>>();
    try (var subReader = this.sectionDataReader()) {
      final int count =
        (int) (subReader.readU32BE("Count") & 0xffff_ffffL);

      for (int index = 0; index < count; ++index) {
        final var keyLength =
          subReader.readU32BE("KeyLength");

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
          subReader.readU32BE("ValueLength");

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

        List<String> values = metadata.get(key);
        if (values == null) {
          values = new ArrayList<>();
        }
        values.add(val);
        metadata.put(key, values);
      }
    }
    return Map.copyOf(metadata);
  }
}
