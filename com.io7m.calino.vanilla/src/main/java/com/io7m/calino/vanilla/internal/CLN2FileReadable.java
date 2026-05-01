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
import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableType;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.supercompression.api.CLNDecompressorFactoryType;
import com.io7m.entomos.core.EoException;
import com.io7m.entomos.core.EoFileReaderType;
import com.io7m.entomos.core.EoFileSection;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;
import com.io7m.junreachable.UnreachableCodeException;

import java.util.Collections;
import java.util.NavigableSet;
import java.util.Objects;

import static com.io7m.calino.api.CLNIdentifiers.sectionEndIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImage2DIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageArrayIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageCubeIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageInfoIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionMetadataIdentifier;

/**
 * The main readable file implementation.
 */

public final class CLN2FileReadable
  implements CLNFileReadableType
{
  private final CLNDecompressorFactoryType decompressors;
  private final BSSReaderRandomAccessType baseReader;
  private final EoFileReaderType reader;
  private final CLNParseRequest request;
  private final NavigableSet<EoFileSection> sections;
  private final NavigableSet<EoFileSection> sectionsRead;

  /**
   * The main readable file implementation.
   *
   * @param inDecompressors The decompressors
   * @param inBaseReader    The base reader
   * @param inReader        The reader
   * @param inRequest       The parse request
   */

  public CLN2FileReadable(
    final CLNDecompressorFactoryType inDecompressors,
    final BSSReaderRandomAccessType inBaseReader,
    final EoFileReaderType inReader,
    final CLNParseRequest inRequest)
  {
    this.decompressors =
      Objects.requireNonNull(inDecompressors, "Decompressors");
    this.baseReader =
      Objects.requireNonNull(inBaseReader, "BaseReader");
    this.reader =
      Objects.requireNonNull(inReader, "Reader");
    this.request =
      Objects.requireNonNull(inRequest, "Request");
    this.sections =
      this.reader.sections();
    this.sectionsRead =
      Collections.unmodifiableNavigableSet(this.sections);
  }

  @Override
  public NavigableSet<EoFileSection> sections()
  {
    this.checkNotClosed();
    return this.sectionsRead;
  }

  @Override
  public CLNVersion version()
  {
    final var fileVersion = this.reader.version();
    return new CLNVersion(fileVersion.major(), fileVersion.minor());
  }

  private void checkNotClosed()
  {
    if (this.baseReader.isClosed()) {
      throw new IllegalStateException("File is closed.");
    }
  }

  @Override
  public CLNSectionReadableType openSection(
    final EoFileSection description)
  {
    this.checkNotClosed();

    if (!this.sections.contains(description)) {
      throw new IllegalArgumentException(
        "File does not contain the provided section.");
    }

    final var identifier = description.tag();
    if (identifier == sectionEndIdentifier()) {
      return new CLN2SectionReadableEnd(
        this.baseReader,
        this.request,
        description
      );
    }

    if (identifier == sectionImageInfoIdentifier()) {
      return new CLN2SectionReadableImageInfo(
        this.baseReader,
        this.request,
        description
      );
    }

    if (identifier == sectionMetadataIdentifier()) {
      return new CLN2SectionReadableMetadata(
        this.baseReader,
        this.request,
        description
      );
    }

    if (identifier == sectionImage2DIdentifier()) {
      return new CLN2SectionReadableImage2D(
        this.decompressors,
        this.baseReader,
        this.request,
        description,
        this::findImageInfo
      );
    }

    if (identifier == sectionImageArrayIdentifier()) {
      return new CLN2SectionReadableImageArray(
        this.decompressors,
        this.baseReader,
        this.request,
        description,
        this::findImageInfo
      );
    }

    if (identifier == sectionImageCubeIdentifier()) {
      return new CLN2SectionReadableImageCube(
        this.decompressors,
        this.baseReader,
        this.request,
        description,
        this::findImageInfo
      );
    }

    return new CLN2SectionReadableOther(
      this.baseReader,
      this.request,
      description
    );
  }

  @Override
  public long trailingOctets()
  {
    return 0L;
  }

  private CLNImageInfo findImageInfo()
    throws CLNException
  {
    for (final var section : this.sections) {
      if (section.tag() == sectionImageInfoIdentifier()) {
        try (var readable =
               (CLNSectionReadableImageInfoType) this.openSection(section)) {
          return readable.info();
        }
      }
    }

    throw new UnreachableCodeException();
  }

  @Override
  public void close()
    throws CLNException
  {
    try {
      this.reader.close();
    } catch (final EoException e) {
      throw CLNException.wrap(e);
    }
  }
}
