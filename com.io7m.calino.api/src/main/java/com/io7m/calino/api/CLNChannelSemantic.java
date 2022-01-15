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

package com.io7m.calino.api;

import java.text.ParseException;

/**
 * The semantic of a channel within an image.
 */

public enum CLNChannelSemantic implements CLNDescribableType
{
  /**
   * The channel represents data on the red axis of an R(GB) image.
   */

  RED {
    @Override
    public String descriptor()
    {
      return "R";
    }
  },

  /**
   * The channel represents data on the green axis of an R(GB) image.
   */

  GREEN {
    @Override
    public String descriptor()
    {
      return "G";
    }
  },

  /**
   * The channel represents data on the blue axis of an R(GB) image.
   */

  BLUE {
    @Override
    public String descriptor()
    {
      return "B";
    }
  },

  /**
   * The channel represents alpha opacity.
   */

  ALPHA {
    @Override
    public String descriptor()
    {
      return "A";
    }
  },

  /**
   * The channel represents depth values.
   */

  DEPTH {
    @Override
    public String descriptor()
    {
      return "D";
    }
  },

  /**
   * The channel represents stencil values.
   */

  STENCIL {
    @Override
    public String descriptor()
    {
      return "S";
    }
  };

  /**
   * Parse the channel semantic from the given channel descriptor.
   *
   * @param descriptor The descriptor
   *
   * @return The channel semantic
   *
   * @throws ParseException On parse errors
   */

  public static CLNChannelSemantic of(
    final String descriptor)
    throws ParseException
  {
    return switch (descriptor) {
      case "R" -> RED;
      case "G" -> GREEN;
      case "B" -> BLUE;
      case "A" -> ALPHA;
      case "D" -> DEPTH;
      case "S" -> STENCIL;
      default -> throw new ParseException(
        "Unrecognized channel semantic: " + descriptor, 0);
    };
  }
}
