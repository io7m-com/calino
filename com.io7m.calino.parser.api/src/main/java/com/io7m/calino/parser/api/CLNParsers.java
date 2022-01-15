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

package com.io7m.calino.parser.api;

import com.io7m.calino.api.CLNVersion;

import java.io.IOException;
import java.net.URI;
import java.nio.channels.SeekableByteChannel;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Objects;
import java.util.Optional;
import java.util.ServiceLoader;

/**
 * The main parser factory.
 */

public final class CLNParsers
{
  private final CLNProbes probes;

  /**
   * The main parser factory.
   */

  public CLNParsers()
  {
    this.probes = new CLNProbes();
  }

  /**
   * Find a parser factory for the given file version.
   *
   * @param version The file version
   *
   * @return A parser factory
   */

  public Optional<CLNParserFactoryType> findParserFactoryFor(
    final CLNVersion version)
  {
    Objects.requireNonNull(version, "version");

    final var loader =
      ServiceLoader.load(CLNParserFactoryType.class);
    final var iterator =
      loader.iterator();
    final var candidates =
      new ArrayList<CLNParserFactoryType>();

    while (iterator.hasNext()) {
      final var factory = iterator.next();
      if (factory.supportedMajorVersion() == version.major()) {
        candidates.add(factory);
      }
    }

    Collections.sort(candidates, (o1, o2) -> {
      return Integer.compareUnsigned(
        o1.highestMinorVersion(),
        o2.highestMinorVersion()
      );
    });

    if (candidates.isEmpty()) {
      return Optional.empty();
    }

    return Optional.of(candidates.get(candidates.size() - 1));
  }

  private record FindResult(
    CLNVersion version,
    Optional<CLNParserFactoryType> factory)
  {

  }

  /**
   * Find a parser factory for the given file. The file will be probed to
   * determine which file version is present.
   *
   * @param channel The file channel
   * @param source  The file source
   *
   * @return A parser factory
   *
   * @throws IOException On errors
   */

  public Optional<CLNParserFactoryType> findParserFactoryFor(
    final SeekableByteChannel channel,
    final URI source)
    throws IOException
  {
    Objects.requireNonNull(channel, "channel");
    Objects.requireNonNull(source, "source");
    return this.probeVersion(channel, source).factory();
  }

  private FindResult probeVersion(
    final SeekableByteChannel channel,
    final URI source)
    throws IOException
  {
    final var probe =
      this.probes.createProbe(source, channel);
    final var version =
      probe.execute();
    final var factoryResult =
      this.findParserFactoryFor(version);
    return new FindResult(version, factoryResult);
  }

  /**
   * Create a parser for the given request.
   *
   * @param request The request
   *
   * @return A parser
   *
   * @throws IOException On errors
   */

  public CLNParserType createParser(
    final CLNParseRequest request)
    throws IOException
  {
    Objects.requireNonNull(request, "request");

    final var result =
      this.probeVersion(request.channel(), request.source());

    final var factoryOpt = result.factory();
    if (factoryOpt.isEmpty()) {
      throw new IOException(
        String.format(
          "No parser available supporting version %s%n",
          result.version.toString()
        ));
    }

    final var factory = factoryOpt.get();
    return factory.createParser(request);
  }
}
