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

import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNFileWritableType;
import com.io7m.calino.api.CLNSectionWritableType;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.jaffirm.core.Preconditions;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.List;
import java.util.Objects;

import static com.io7m.calino.api.CLNIdentifiers.sectionEndIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImage2DIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageArrayIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageInfoIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionMetadataIdentifier;

/**
 * The main writable file implementation.
 */

public final class CLN1FileWritable implements CLNFileWritableType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN1FileWritable.class);

  private final BSSWriterRandomAccessType writer;
  private final CLNWriteRequest request;
  private final BSSWriterProviderType writers;
  private CLNSectionWritableType sectionOpen;
  private long sectionLastClosed;

  CLN1FileWritable(
    final BSSWriterProviderType inWriters,
    final BSSWriterRandomAccessType inWriter,
    final CLNWriteRequest inRequest)
  {
    this.writers =
      Objects.requireNonNull(inWriters, "writers");
    this.writer =
      Objects.requireNonNull(inWriter, "writer");
    this.request =
      Objects.requireNonNull(inRequest, "request");
  }

  @Override
  public List<CLNFileSectionDescription> sections()
    throws IOException
  {
    throw new IOException();
  }

  @Override
  public CLNVersion version()
  {
    return this.request.version();
  }

  @Override
  public CLNSectionWritableType createSection(
    final long identifier)
    throws IOException
  {
    if (this.sectionOpen != null) {
      throw new IllegalStateException(
        String.format(
          "Section %s is already open for writing", this.sectionOpen));
    }

    final var offsetCurrentAbsolute =
      this.writer.offsetCurrentAbsolute();

    Preconditions.checkPreconditionV(
      offsetCurrentAbsolute % 16L == 0L,
      "Sections must be aligned to 16 octet boundaries (offset is %s)",
      Long.toUnsignedString(offsetCurrentAbsolute, 16)
    );
    Preconditions.checkPreconditionV(
      Long.compareUnsigned(offsetCurrentAbsolute, this.sectionLastClosed) >= 0,
      "Offset %s would damage existing section that closed at %s",
      Long.toUnsignedString(offsetCurrentAbsolute),
      Long.toUnsignedString(this.sectionLastClosed)
    );

    final var section =
      this.openTypedSection(identifier);

    this.writer.writeU64BE(identifier);
    this.writer.writeU64BE(0L);
    return section;
  }

  private CLN1SectionWritableAbstract openTypedSection(
    final long identifier)
  {
    if (identifier == sectionEndIdentifier()) {
      return new CLN1SectionWritableEnd(
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }
    if (identifier == sectionImageInfoIdentifier()) {
      return new CLN1SectionWritableImageInfo(
        this.writers,
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }
    if (identifier == sectionMetadataIdentifier()) {
      return new CLN1SectionWritableMetadata(
        this.writers,
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }
    if (identifier == sectionImage2DIdentifier()) {
      return new CLN1SectionWritableImage2D(
        this.writers,
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }
    if (identifier == sectionImageArrayIdentifier()) {
      return new CLN1SectionWritableImageArray(
        this.writers,
        this.writer,
        this.request,
        identifier,
        this::onSectionClosed
      );
    }

    return new CLN1SectionWritableOther(
      this.writer,
      this.request,
      identifier,
      this::onSectionClosed
    );
  }

  private void onSectionClosed(
    final CLNSectionWritableType section)
  {
    if (LOG.isTraceEnabled()) {
      LOG.trace(
        "closed section 0x{} @ {}",
        Long.toUnsignedString(section.identifier(), 16),
        Long.toUnsignedString(this.writer.offsetCurrentAbsolute())
      );
    }

    this.sectionLastClosed = this.writer.offsetCurrentAbsolute();
    this.sectionOpen = null;
  }

  @Override
  public void close()
    throws IOException
  {
    this.writer.close();
  }
}
