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

import com.io7m.calino.vanilla.internal.CLNByteBufferByteChannel;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.ClosedChannelException;
import java.util.Arrays;

import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class CLNByteBufferChannelTest
{
  @Test
  public void testReadWrite()
    throws IOException
  {
    final var bufferBytes =
      new byte[13];
    final var buffer =
      ByteBuffer.wrap(bufferBytes);
    final var channel =
      new CLNByteBufferByteChannel(buffer);

    assertTrue(channel.isOpen());

    channel.write(ByteBuffer.wrap("HELLO".getBytes(UTF_8)));
    assertEquals(5L, channel.position());
    channel.write(ByteBuffer.wrap("THERE".getBytes(UTF_8)));
    assertEquals(10L, channel.position());
    channel.write(ByteBuffer.wrap("YOU".getBytes(UTF_8)));
    assertEquals(13L, channel.position());

    channel.position(0L);
    assertEquals(0L, channel.position());
    assertEquals(13L, channel.size());

    channel.truncate(0L);

    {
      final var srcBytes = new byte[5];
      Arrays.fill(srcBytes, (byte) 'z');

      final var src = ByteBuffer.wrap(srcBytes);
      final var read = channel.read(src);
      assertEquals(5, read);
      assertEquals(5L, channel.position());
      assertEquals("HELLO", new String(srcBytes, UTF_8));
    }

    {
      final var srcBytes = new byte[5];
      Arrays.fill(srcBytes, (byte) 'z');

      final var src = ByteBuffer.wrap(srcBytes);
      final var read = channel.read(src);
      assertEquals(5, read);
      assertEquals(10L, channel.position());
      assertEquals("THERE", new String(srcBytes, UTF_8));
    }

    {
      final var srcBytes = new byte[5];
      Arrays.fill(srcBytes, (byte) 'z');

      final var src = ByteBuffer.wrap(srcBytes);
      final var read = channel.read(src);
      assertEquals(3, read);
      assertEquals(13L, channel.position());
      assertEquals("YOUzz", new String(srcBytes, UTF_8));
    }

    assertTrue(channel.isOpen());
    channel.close();
    assertFalse(channel.isOpen());
    assertThrows(ClosedChannelException.class, channel::position);
  }
}
