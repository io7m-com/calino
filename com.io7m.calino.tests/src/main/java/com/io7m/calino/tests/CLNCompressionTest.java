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

package com.io7m.calino.tests;

import com.io7m.calino.api.CLNImage2DDescription;
import com.io7m.calino.api.CLNSuperCompressionMethodCustom;
import com.io7m.calino.supercompression.api.CLNCompressorRequest;
import com.io7m.calino.supercompression.api.CLNCompressors;
import com.io7m.calino.supercompression.api.CLNDecompressorRequest;
import com.io7m.calino.supercompression.api.CLNDecompressors;
import com.io7m.wendover.core.ByteBufferChannels;
import org.junit.jupiter.api.Test;

import java.nio.ByteBuffer;

import static org.junit.jupiter.api.Assertions.assertThrows;

public final class CLNCompressionTest
{
  @Test
  public void testUnsupportedCompression()
  {
    final var compressors = new CLNCompressors();

    assertThrows(UnsupportedOperationException.class, () -> {
      compressors.createCompressor(new CLNCompressorRequest(
        new CLNSuperCompressionMethodCustom("What?", 0L)
      ));
    });
  }

  @Test
  public void testUnsupportedDecompression()
  {
    final var decompressors = new CLNDecompressors();

    assertThrows(UnsupportedOperationException.class, () -> {
      decompressors.createDecompressor(new CLNDecompressorRequest(
        new CLNSuperCompressionMethodCustom("What?", 0L),
        new CLNImage2DDescription(
          0, 0L, 100L, 100L, 0
        ),
        ByteBufferChannels.ofByteBuffer(ByteBuffer.allocate(100))
      ));
    });
  }
}
