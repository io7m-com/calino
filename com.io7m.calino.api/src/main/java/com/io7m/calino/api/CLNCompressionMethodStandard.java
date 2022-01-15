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

/**
 * The standard compression methods.
 */

public enum CLNCompressionMethodStandard
  implements CLNCompressionMethodType
{
  /**
   * No compression.
   */

  UNCOMPRESSED {
    @Override
    public String descriptor()
    {
      return "UNCOMPRESSED";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 0;
    }

    @Override
    public int blockSizeY()
    {
      return 0;
    }

    @Override
    public int blockAlignment()
    {
      return 0;
    }
  },

  /**
   * BC1 compression (otherwise known as DXT1 compression).
   */

  BC1 {
    @Override
    public String descriptor()
    {
      return "BC1";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 8;
    }
  },

  /**
   * BC2 compression (otherwise known as DXT3 compression).
   */

  BC2 {
    @Override
    public String descriptor()
    {
      return "BC2";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 16;
    }
  },

  /**
   * BC3 compression (otherwise known as DXT5 compression).
   */

  BC3 {
    @Override
    public String descriptor()
    {
      return "BC3";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 16;
    }
  },

  /**
   * BC4 compression.
   */

  BC4 {
    @Override
    public String descriptor()
    {
      return "BC4";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 8;
    }
  },

  /**
   * BC5 compression.
   */

  BC5 {
    @Override
    public String descriptor()
    {
      return "BC5";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 16;
    }
  },

  /**
   * BC6 compression.
   */

  BC6 {
    @Override
    public String descriptor()
    {
      return "BC6";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 16;
    }
  },

  /**
   * BC7 compression.
   */

  BC7 {
    @Override
    public String descriptor()
    {
      return "BC7";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 16;
    }
  },

  /**
   * ETC1 compression.
   */

  ETC1 {
    @Override
    public String descriptor()
    {
      return "ETC1";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 16;
    }
  },

  /**
   * ETC2 compression.
   */

  ETC2 {
    @Override
    public String descriptor()
    {
      return "ETC2";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 16;
    }
  },

  /**
   * EAC compression.
   */

  EAC {
    @Override
    public String descriptor()
    {
      return "EAC";
    }

    @Override
    public long compressionSectionIdentifier()
    {
      return 0L;
    }

    @Override
    public int blockSizeX()
    {
      return 4;
    }

    @Override
    public int blockSizeY()
    {
      return 4;
    }

    @Override
    public int blockAlignment()
    {
      return 16;
    }
  }
}
