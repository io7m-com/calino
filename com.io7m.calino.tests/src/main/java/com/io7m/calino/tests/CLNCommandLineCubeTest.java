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

import com.io7m.calino.api.CLNByteOrder;
import com.io7m.calino.api.CLNChannelsLayoutDescriptionStandard;
import com.io7m.calino.api.CLNChannelsLayoutDescriptionType;
import com.io7m.calino.api.CLNSuperCompressionMethodStandard;
import com.io7m.calino.api.CLNSuperCompressionMethodType;
import com.io7m.calino.cmdline.CLNMain;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import java.util.stream.Stream;

import static java.nio.charset.StandardCharsets.UTF_8;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.WRITE;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeout;

public final class CLNCommandLineCubeTest
{
  private Path directory;
  private ByteArrayOutputStream outLog;
  private PrintStream outPrint;
  private PrintStream outSaved;
  private ByteArrayOutputStream errLog;
  private PrintStream errPrint;
  private PrintStream errSaved;
  private Path directoryOutput;

  @BeforeEach
  public void setup()
    throws IOException
  {
    this.directory =
      CLNTestDirectories.createTempDirectory();
    this.directoryOutput =
      this.directory.resolve("outputs");

    this.errLog = new ByteArrayOutputStream();
    this.errPrint = new PrintStream(this.errLog, true, UTF_8);
    this.outLog = new ByteArrayOutputStream();
    this.outPrint = new PrintStream(this.outLog, true, UTF_8);

    this.errSaved = System.err;
    this.outSaved = System.out;
    System.setOut(this.outPrint);
    System.setErr(this.errPrint);
  }

  @AfterEach
  public void tearDown()
    throws IOException
  {
    this.outPrint.flush();
    this.errPrint.flush();

    System.setOut(this.outSaved);
    System.setErr(this.errSaved);

    CLNTestDirectories.deleteDirectory(this.directory);

    System.out.println("OUT: ");
    System.out.println(this.outLog.toString(UTF_8));
    System.out.println();
    System.out.println("ERR: ");
    System.out.println(this.errLog.toString(UTF_8));
    System.out.println();
    System.out.flush();
  }

  private Stream<ImageFormatTestCase> imageFormatTestCases()
    throws IOException
  {
    final var files =
      List.of(
        "produce8.png",
        "produce16.png",
        "produceFade8.png",
        "produceFade16.png",
        "produceGrey8.png",
        "produceGrey16.png"
      );

    final var cases = new ArrayList<ImageFormatTestCase>(256);
    for (final var name : files) {
      final var path =
        CLNTestDirectories.resourceOf(
          CLN1ParsersContract.class,
          this.directory,
          name
        );

      for (final var order : CLNByteOrder.values()) {
        for (final var compression : CLNSuperCompressionMethodStandard.values()) {
          for (final var layout : CLNChannelsLayoutDescriptionStandard.values()) {
            cases.add(
              new ImageFormatTestCase(name, path, order, compression, layout)
            );
          }
        }
      }
    }

    return cases.stream();
  }


  private DynamicTest createCreationTestCaseCube(
    final ImageFormatTestCase testCase)
  {
    final var testName =
      new StringBuilder(128)
        .append("testCreateExhaustionCube_")
        .append(testCase.name)
        .append("|")
        .append(testCase.layout.descriptor())
        .append("|")
        .append(testCase.superCompression.descriptor())
        .append("|")
        .append(testCase.byteOrder.name())
        .toString();

    return DynamicTest.dynamicTest(
      testName,
      () -> {
        final var properties = new Properties();
        properties.put("test", testName);

        final var propsFile =
          this.directory.resolve("test.properties");
        try (var writer =
               Files.newBufferedWriter(propsFile, CREATE, WRITE)) {
          properties.store(writer, "");
        }

        assertTimeout(Duration.ofSeconds(10L), () -> {
          final var r = CLNMain.mainExitless(new String[]{
            "create-cube",
            "--verbose",
            "trace",
            "--metadata",
            propsFile.toAbsolutePath().toString(),
            "--source-x-positive",
            testCase.file.toAbsolutePath().toString(),
            "--source-x-negative",
            testCase.file.toAbsolutePath().toString(),
            "--source-y-positive",
            testCase.file.toAbsolutePath().toString(),
            "--source-y-negative",
            testCase.file.toAbsolutePath().toString(),
            "--source-z-positive",
            testCase.file.toAbsolutePath().toString(),
            "--source-z-negative",
            testCase.file.toAbsolutePath().toString(),
            "--output",
            this.directory.resolve("output.ctf").toString(),
            "--convert-layout-to",
            testCase.layout.descriptor(),
            "--byte-order",
            testCase.byteOrder.name(),
            "--super-compression",
            testCase.superCompression.descriptor()
          });
          assertEquals(0, r);
        });

        assertTimeout(Duration.ofSeconds(10L), () -> {
          final var r = CLNMain.mainExitless(new String[]{
            "check",
            "--verbose",
            "trace",
            "--warnings-as-errors",
            "true",
            "--file",
            this.directory.resolve("output.ctf").toString(),
          });
          assertEquals(0, r);
        });

        assertTimeout(Duration.ofSeconds(10L), () -> {
          final var r = CLNMain.mainExitless(new String[]{
            "extract-image-data-cube",
            "--verbose",
            "trace",
            "--file",
            this.directory.resolve("output.ctf").toString(),
            "--output-directory",
            this.directoryOutput.toString(),
            "--decompress",
            "true",
            "--output-format",
            "PNG"
          });
          assertEquals(0, r);
        });

        assertTimeout(Duration.ofSeconds(10L), () -> {
          final var r = CLNMain.mainExitless(new String[]{
            "extract-image-data-cube",
            "--verbose",
            "trace",
            "--file",
            this.directory.resolve("output.ctf").toString(),
            "--output-directory",
            this.directoryOutput.toString(),
            "--decompress",
            "true",
            "--output-format",
            "RAW"
          });
          assertEquals(0, r);
        });
      }
    );
  }


  @TestFactory
  public Stream<DynamicTest> testCreateAllFormatCasesCube()
    throws IOException
  {
    return this.imageFormatTestCases()
      .map(this::createCreationTestCaseCube);
  }

  private record ImageFormatTestCase(
    String name,
    Path file,
    CLNByteOrder byteOrder,
    CLNSuperCompressionMethodType superCompression,
    CLNChannelsLayoutDescriptionType layout)
  {

  }
}
