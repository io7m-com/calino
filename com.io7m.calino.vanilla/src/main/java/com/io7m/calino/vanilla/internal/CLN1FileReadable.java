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

import com.io7m.calino.api.CLNFileReadableType;
import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNImageInfo;
import com.io7m.calino.api.CLNSectionReadableImageInfoType;
import com.io7m.calino.api.CLNSectionReadableType;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.parser.api.CLNParseRequest;
import com.io7m.calino.supercompression.api.CLNDecompressorFactoryType;
import com.io7m.jbssio.api.BSSReaderRandomAccessType;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static com.io7m.calino.api.CLNIdentifiers.sectionEndIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImage2DIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageArrayIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageInfoIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionMetadataIdentifier;

/**
 * The main readable file implementation.
 */

public final class CLN1FileReadable implements CLNFileReadableType
{
  private final CLNDecompressorFactoryType decompressors;
  private final BSSReaderRandomAccessType reader;
  private final CLNParseRequest request;
  private final CLNVersion version;
  private final List<CLNFileSectionDescription> fileSections;

  CLN1FileReadable(
    final CLNDecompressorFactoryType inDecompressors,
    final BSSReaderRandomAccessType inReader,
    final CLNParseRequest inRequest,
    final CLNVersion inVersion,
    final ArrayList<CLNFileSectionDescription> inFileSections)
  {
    this.decompressors =
      Objects.requireNonNull(inDecompressors, "inDecompressors");
    this.reader =
      Objects.requireNonNull(inReader, "reader");
    this.request =
      Objects.requireNonNull(inRequest, "request");
    this.version =
      Objects.requireNonNull(inVersion, "version");
    this.fileSections =
      List.copyOf(
        Objects.requireNonNull(inFileSections, "fileSections"));
  }

  @Override
  public List<CLNFileSectionDescription> sections()
  {
    this.checkNotClosed();
    return this.fileSections;
  }

  @Override
  public CLNVersion version()
  {
    return this.version;
  }

  private void checkNotClosed()
  {
    if (this.reader.isClosed()) {
      throw new IllegalStateException("File is closed.");
    }
  }

  @Override
  public CLNSectionReadableType openSection(
    final CLNFileSectionDescription description)
  {
    this.checkNotClosed();

    if (!this.fileSections.contains(description)) {
      throw new IllegalArgumentException(
        "File does not contain the provided section.");
    }

    final var identifier =
      description.description().identifier();

    if (identifier == sectionEndIdentifier()) {
      return new CLN1SectionReadableEnd(
        this.reader,
        this.request,
        description
      );
    }

    if (identifier == sectionImageInfoIdentifier()) {
      return new CLN1SectionReadableImageInfo(
        this.reader,
        this.request,
        description
      );
    }

    if (identifier == sectionMetadataIdentifier()) {
      return new CLN1SectionReadableMetadata(
        this.reader,
        this.request,
        description
      );
    }

    if (identifier == sectionImage2DIdentifier()) {
      return new CLN1SectionReadableImage2D(
        this.decompressors,
        this.reader,
        this.request,
        description,
        this::findImageInfo
      );
    }

    if (identifier == sectionImageArrayIdentifier()) {
      return new CLN1SectionReadableImageArray(
        this.decompressors,
        this.reader,
        this.request,
        description,
        this::findImageInfo
      );
    }

    return new CLN1SectionReadableOther(this.reader, this.request, description);
  }

  private CLNImageInfo findImageInfo()
    throws IOException
  {
    for (final var fileSection : this.fileSections) {
      final var description = fileSection.description();
      if (description.identifier() == sectionImageInfoIdentifier()) {
        try (var section = (CLNSectionReadableImageInfoType) this.openSection(
          fileSection)) {
          return section.info();
        }
      }
    }
    throw new IOException(
      "The current file does not appear to contain a usable image info section.");
  }

  @Override
  public void close()
    throws IOException
  {
    this.reader.close();
  }
}
