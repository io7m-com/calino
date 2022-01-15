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

import com.io7m.calino.supercompression.lz4.CLNSupercompressionLZ4;
import com.io7m.calino.supercompression.spi.CLNCompressorSPIFactoryType;
import com.io7m.calino.supercompression.spi.CLNDecompressorSPIFactoryType;

/**
 * Calino texture format (LZ4 Decompressor).
 */

module com.io7m.calino.supercompression.lz4
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires transitive com.io7m.calino.api;
  requires transitive com.io7m.calino.supercompression.spi;

  requires org.apache.commons.io;
  requires org.lz4.java;
  requires org.slf4j;

  provides CLNDecompressorSPIFactoryType
    with CLNSupercompressionLZ4;
  provides CLNCompressorSPIFactoryType
    with CLNSupercompressionLZ4;

  exports com.io7m.calino.supercompression.lz4;
}
