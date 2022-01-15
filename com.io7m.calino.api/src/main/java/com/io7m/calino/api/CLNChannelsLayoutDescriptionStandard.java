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

import java.util.List;

import static com.io7m.calino.api.CLNChannelSemantic.ALPHA;
import static com.io7m.calino.api.CLNChannelSemantic.BLUE;
import static com.io7m.calino.api.CLNChannelSemantic.GREEN;
import static com.io7m.calino.api.CLNChannelSemantic.RED;

/**
 * The set of standard channel layouts.
 */

public enum CLNChannelsLayoutDescriptionStandard
  implements CLNChannelsLayoutDescriptionType
{
  /**
   * The RGB565 format.
   */

  R5_G6_B5 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 5),
        new CLNChannelDescription(GREEN, 6),
        new CLNChannelDescription(BLUE, 5)
      );
    }
  },

  /**
   * The RGBA4444 format.
   */

  R4_G4_B4_A4 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 4),
        new CLNChannelDescription(GREEN, 4),
        new CLNChannelDescription(BLUE, 4),
        new CLNChannelDescription(ALPHA, 4)
      );
    }
  },

  /**
   * The R8 format.
   */

  R8 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 8)
      );
    }
  },

  /**
   * The RG8 format.
   */

  R8_G8 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 8),
        new CLNChannelDescription(GREEN, 8)
      );
    }
  },

  /**
   * The RGB8 format.
   */

  R8_G8_B8 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 8),
        new CLNChannelDescription(GREEN, 8),
        new CLNChannelDescription(BLUE, 8)
      );
    }
  },

  /**
   * The RGBA8 format.
   */

  R8_G8_B8_A8 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 8),
        new CLNChannelDescription(GREEN, 8),
        new CLNChannelDescription(BLUE, 8),
        new CLNChannelDescription(ALPHA, 8)
      );
    }
  },

  /**
   * The R16 format.
   */

  R16 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 16)
      );
    }
  },

  /**
   * The RG16 format.
   */

  R16_G16 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 16),
        new CLNChannelDescription(GREEN, 16)
      );
    }
  },

  /**
   * The RGB16 format.
   */

  R16_G16_B16 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 16),
        new CLNChannelDescription(GREEN, 16),
        new CLNChannelDescription(BLUE, 16)
      );
    }
  },

  /**
   * The RGBA16 format.
   */

  R16_G16_B16_A16 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 16),
        new CLNChannelDescription(GREEN, 16),
        new CLNChannelDescription(BLUE, 16),
        new CLNChannelDescription(ALPHA, 16)
      );
    }
  },

  /**
   * The R32 format.
   */

  R32 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 32)
      );
    }
  },

  /**
   * The RG32 format.
   */

  R32_G32 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 32),
        new CLNChannelDescription(GREEN, 32)
      );
    }
  },

  /**
   * The RGB32 format.
   */

  R32_G32_B32 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 32),
        new CLNChannelDescription(GREEN, 32),
        new CLNChannelDescription(BLUE, 32)
      );
    }
  },

  /**
   * The RGBA32 format.
   */

  R32_G32_B32_A32 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 32),
        new CLNChannelDescription(GREEN, 32),
        new CLNChannelDescription(BLUE, 32),
        new CLNChannelDescription(ALPHA, 32)
      );
    }
  },

  /**
   * The R64 format.
   */

  R64 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 64)
      );
    }
  },

  /**
   * The RG64 format.
   */

  R64_G64 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 64),
        new CLNChannelDescription(GREEN, 64)
      );
    }
  },

  /**
   * The RGB64 format.
   */

  R64_G64_B64 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 64),
        new CLNChannelDescription(GREEN, 64),
        new CLNChannelDescription(BLUE, 64)
      );
    }
  },

  /**
   * The RGBA64 format.
   */

  R64_G64_B64_A64 {
    @Override
    public List<CLNChannelDescription> channels()
    {
      return List.of(
        new CLNChannelDescription(RED, 64),
        new CLNChannelDescription(GREEN, 64),
        new CLNChannelDescription(BLUE, 64),
        new CLNChannelDescription(ALPHA, 64)
      );
    }
  }
}
