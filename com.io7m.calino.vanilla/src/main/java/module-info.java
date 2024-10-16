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

/**
 * Calino texture format (Vanilla implementation)
 */

module com.io7m.calino.vanilla
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires transitive com.io7m.calino.api;
  requires transitive com.io7m.calino.parser.api;
  requires transitive com.io7m.calino.supercompression.api;
  requires transitive com.io7m.calino.validation.api;
  requires transitive com.io7m.calino.writer.api;

  requires com.io7m.jaffirm.core;
  requires com.io7m.jbssio.api;
  requires com.io7m.junreachable.core;
  requires com.io7m.jxtrand.vanilla;
  requires com.io7m.wendover.core;
  requires org.slf4j;

  opens com.io7m.calino.vanilla.internal
    to com.io7m.jxtrand.vanilla;

  uses com.io7m.jbssio.api.BSSReaderProviderType;
  uses com.io7m.jbssio.api.BSSWriterProviderType;

  provides com.io7m.calino.parser.api.CLNParserFactoryType
    with com.io7m.calino.vanilla.CLN1Parsers;
  provides com.io7m.calino.writer.api.CLNWriterFactoryType
    with com.io7m.calino.vanilla.CLN1Writers;
  provides com.io7m.calino.validation.api.CLNValidatorFactoryType
    with com.io7m.calino.vanilla.CLN1Validators;

  exports com.io7m.calino.vanilla;
}
