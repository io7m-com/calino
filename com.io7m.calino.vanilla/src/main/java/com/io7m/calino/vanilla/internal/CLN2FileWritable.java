/*
 * Copyright © 2026 Mark Raynsford <code@io7m.com> https://www.io7m.com
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
import com.io7m.calino.api.CLNFileSectionDescription;
import com.io7m.calino.api.CLNFileWritableType;
import com.io7m.calino.api.CLNIdentifiers;
import com.io7m.calino.api.CLNSectionWritableType;
import com.io7m.calino.api.CLNVersion;
import com.io7m.calino.writer.api.CLNWriteRequest;
import com.io7m.jbssio.api.BSSWriterProviderType;
import com.io7m.jbssio.api.BSSWriterRandomAccessType;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.seltzer.io.SIOException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.calino.api.CLNIdentifiers.sectionEndIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImage2DIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageArrayIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageCubeIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionImageInfoIdentifier;
import static com.io7m.calino.api.CLNIdentifiers.sectionMetadataIdentifier;

/**
 * The main writable file implementation.
 */

public final class CLN2FileWritable
  implements CLNFileWritableType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(CLN2FileWritable.class);

  private final BSSWriterRandomAccessType writer;
  private final CLNWriteRequest request;
  private final BSSWriterProviderType writers;
  private final CloseableCollectionType<CLNException> resources;
  private CLN2SectionWritableAbstract sectionOpen;

  /**
   * The main writable file implementation.
   *
   * @param inWriters The write provider
   * @param inWriter  The main writer
   * @param inRequest The write request
   */

  CLN2FileWritable(
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

    this.resources =
      CloseableCollection.create(() -> {
        return new CLNException(
          "One or more resources could not be closed.",
          Map.of(),
          "error-resource-close",
          Optional.empty()
        );
      });
  }

  @Override
  public List<CLNFileSectionDescription> sections()
    throws IOException
  {
    return List.of();
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

    final var section = this.openTypedSection(identifier);
    this.sectionOpen = section;
    return section;
  }

  private CLN2SectionWritableAbstract openTypedSection(
    final long identifier)
    throws IOException
  {
    if (identifier == sectionEndIdentifier()) {
      return new CLN2SectionWritableEnd(this.resources, this::onSectionClosed);
    }
    if (identifier == sectionImageInfoIdentifier()) {
      return new CLN2SectionWritableImageInfo(
        this.resources,
        this::onSectionClosed);
    }
    if (identifier == sectionMetadataIdentifier()) {
      return new CLN2SectionWritableMetadata(
        this.resources,
        this::onSectionClosed);
    }
    if (identifier == sectionImage2DIdentifier()) {
      return new CLN2SectionWritableImage2D(
        this.resources,
        this::onSectionClosed);
    }
    if (identifier == sectionImageArrayIdentifier()) {
      return new CLN2SectionWritableImageArray(
        this.resources,
        this::onSectionClosed);
    }
    if (identifier == sectionImageCubeIdentifier()) {
      return new CLN2SectionWritableImageCube(
        this.resources,
        this::onSectionClosed);
    }
    return new CLN2SectionWritableOther(
      identifier,
      this.resources,
      this::onSectionClosed);
  }

  private void onSectionClosed(
    final CLN2SectionWritableAbstract section)
    throws CLNException
  {
    try {
      final var data = section.sectionData();

      if (LOG.isTraceEnabled()) {
        LOG.trace(
          "Closed section 0x{} ({}) @ {} (size {})",
          Long.toUnsignedString(section.identifier(), 16),
          CLNIdentifiers.nameOf(section.identifier()),
          Long.toUnsignedString(this.writer.offsetCurrentAbsolute()),
          Long.valueOf(data.size())
        );
      }

      this.writer.writeU64BE(section.identifier());
      this.writer.writeU64BE(data.size());
      this.writer.writeByteChannel(data);
      this.writer.align(16);
      this.sectionOpen = null;
    } catch (final IOException e) {
      throw CLNException.wrap(e);
    }
  }

  @Override
  public void close()
    throws CLNException
  {
    this.resources.close();
  }

  /**
   * Start the section.
   *
   * @throws SIOException On errors
   */

  public void start()
    throws SIOException
  {
    this.writer.seekTo(0L);
    this.writer.writeU64BE(CLNIdentifiers.fileIdentifier());
    this.writer.writeU32BE(2L);
    this.writer.writeU32BE(0L);
  }
}
