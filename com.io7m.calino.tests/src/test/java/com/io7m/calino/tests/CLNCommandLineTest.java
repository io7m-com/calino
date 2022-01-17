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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeout;

public final class CLNCommandLineTest
{
  private Path directory;
  private ByteArrayOutputStream outLog;
  private PrintStream outPrint;
  private PrintStream outSaved;
  private ByteArrayOutputStream errLog;
  private PrintStream errPrint;
  private PrintStream errSaved;

  @BeforeEach
  public void setup()
    throws IOException
  {
    this.directory = CLNTestDirectories.createTempDirectory();

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

  @Test
  public void testNoArguments()
  {
    final var r = CLNMain.mainExitless(new String[]{

    });
    assertEquals(1, r);
  }

  @Test
  public void testVersion()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "version"
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowSummary()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "show-summary"
    });
    assertEquals(1, r);
  }

  @Test
  public void testShowSections()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "show-sections"
    });
    assertEquals(1, r);
  }

  @Test
  public void testShowVersion()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "show-version"
    });
    assertEquals(1, r);
  }

  @Test
  public void testShowMetadata()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "show-metadata"
    });
    assertEquals(1, r);
  }

  @Test
  public void testCheck()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "check"
    });
    assertEquals(1, r);
  }

  @Test
  public void testCreate()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "create"
    });
    assertEquals(1, r);
  }

  @Test
  public void testHelp()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "help"
    });
    assertEquals(0, r);
  }

  @Test
  public void testHelpHelp()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "help",
      "help"
    });
    assertEquals(0, r);
  }

  @Test
  public void testHelpVersion()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "help",
      "version"
    });
    assertEquals(0, r);
  }

  @Test
  public void testHelpShowSummary()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "help",
      "show-summary"
    });
    assertEquals(0, r);
  }

  @Test
  public void testHelpShowVersion()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "help",
      "show-version"
    });
    assertEquals(0, r);
  }

  @Test
  public void testHelpShowSections()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "help",
      "show-sections"
    });
    assertEquals(0, r);
  }

  @Test
  public void testHelpShowMetadata()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "help",
      "show-metadata"
    });
    assertEquals(0, r);
  }

  @Test
  public void testHelpCheck()
  {
    final var r = CLNMain.mainExitless(new String[]{
      "help",
      "check"
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowSectionsBasic()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "basic.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-sections",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowSectionsWarn()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "warn-unaligned.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-sections",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowVersionBasic()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "basic.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-version",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowVersionWarn()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "warn-unaligned.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-version",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowSummaryBasic()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "basic.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-summary",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowSummaryWarn()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "warn-unaligned.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-summary",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(0, r);
  }

  @Test
  public void testExtractImageDataBasic()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "basic.ctf"
      );

    final var outputPath =
      this.directory.resolve("output.bin").toAbsolutePath();

    final var r = CLNMain.mainExitless(new String[]{
      "extract-image-data",
      "--file",
      file.toAbsolutePath().toString(),
      "--output-file",
      outputPath.toString(),
      "--decompress",
      "true"
    });
    assertEquals(0, r);
    assertEquals(3072L, Files.size(outputPath));
  }

  @Test
  public void testExtractImageDataBasicRaw()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "basic.ctf"
      );

    final var outputPath =
      this.directory.resolve("output.bin").toAbsolutePath();

    final var r = CLNMain.mainExitless(new String[]{
      "extract-image-data",
      "--file",
      file.toAbsolutePath().toString(),
      "--output-file",
      outputPath.toString(),
      "--decompress",
      "false"
    });
    assertEquals(0, r);
    assertEquals(3072L, Files.size(outputPath));
  }

  @Test
  public void testShowImageInfoBasic()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "basic.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-image-info",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowImageInfoWarn()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "warn-unaligned.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-image-info",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(1, r);
  }

  @Test
  public void testCreateFromProduce8_0()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--verbose",
      "trace"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_Unsupported0()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8:B8",
      "--verbose",
      "trace"
    });
    assertEquals(1, r);
  }

  @Test
  public void testCreateFromProduce8_RGBA8()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8:G8:B8:A8",
      "--verbose",
      "trace"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_RGB8()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8:G8:B8",
      "--verbose",
      "trace"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_RG8()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8:G8",
      "--verbose",
      "trace"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_R8()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8",
      "--verbose",
      "trace"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_RGBA4444()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "p16|R4:G4:B4:A4",
      "--verbose",
      "trace"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_RGB565()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "p16|R5:G6:B5",
      "--verbose",
      "trace"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_MipMap0()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--mipmap-generate",
      "NEAREST"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_MipMapRGBA8()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8:G8:B8:A8",
      "--mipmap-generate",
      "NEAREST"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_MipMapRGB8()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8:G8:B8",
      "--mipmap-generate",
      "NEAREST"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_MipMapRG8()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8:G8",
      "--mipmap-generate",
      "NEAREST"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_MipMapR8()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8",
      "--mipmap-generate",
      "NEAREST"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_MipMapRGBA4444()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "p16|R4:G4:B4:A4",
      "--mipmap-generate",
      "NEAREST",
      "--verbose",
      "trace"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce8_MipMapRGB565()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "p16|R5:G6:B5",
      "--mipmap-generate",
      "NEAREST",
      "--verbose",
      "trace"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromUnusableFormatVersion()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--format-version",
      "99999999.0",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString()
    });
    assertEquals(1, r);
  }

  @Test
  public void testCreateFromProduceFade8_RGBA8()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produceFade8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8:G8:B8:A8"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduceFade8_RGBA8PreMult()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produceFade8.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString(),
      "--convert-layout-to",
      "R8:G8:B8:A8",
      "--premultiply-alpha",
      "true"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCreateFromProduce16_0()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "produce16.png"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "create",
      "--source",
      file.toAbsolutePath().toString(),
      "--output",
      this.directory.resolve("output.ctf").toString()
    });
    assertEquals(0, r);
  }

  private record ImageFormatTestCase(
    String name,
    Path file,
    CLNByteOrder byteOrder,
    CLNSuperCompressionMethodType superCompression,
    CLNChannelsLayoutDescriptionType layout)
  {

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

  private DynamicTest createCreationTestCase(
    final ImageFormatTestCase testCase)
  {
    return DynamicTest.dynamicTest(
      new StringBuilder(128)
        .append("testCreateExhaustion_")
        .append(testCase.name)
        .append("|")
        .append(testCase.layout.descriptor())
        .append("|")
        .append(testCase.superCompression.descriptor())
        .append("|")
        .append(testCase.byteOrder.name())
        .toString(),
      () -> {
        assertTimeout(Duration.ofSeconds(10L), () -> {
          final var r = CLNMain.mainExitless(new String[]{
            "create",
            "--verbose",
            "trace",
            "--source",
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
            "extract-image-data",
            "--verbose",
            "trace",
            "--file",
            this.directory.resolve("output.ctf").toString(),
            "--output-file",
            this.directory.resolve("output.png").toString(),
            "--decompress",
            "true",
            "--output-format",
            "PNG"
          });
          assertEquals(0, r);
        });

        assertTimeout(Duration.ofSeconds(10L), () -> {
          final var r = CLNMain.mainExitless(new String[]{
            "extract-image-data",
            "--verbose",
            "trace",
            "--file",
            this.directory.resolve("output.ctf").toString(),
            "--output-file",
            this.directory.resolve("output.bin").toString(),
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
  public Stream<DynamicTest> testCreateAllFormatCases()
    throws IOException
  {
    return this.imageFormatTestCases()
      .map(this::createCreationTestCase);
  }

  @Test
  public void testCheckWarningFails()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "warn-unaligned.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "check",
      "--file",
      file.toAbsolutePath().toString(),
      "--warnings-as-errors",
      "true"
    });
    assertEquals(1, r);
  }

  @Test
  public void testCheckEmpty()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "empty.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "check",
      "--file",
      file.toAbsolutePath().toString(),
      "--warnings-as-errors",
      "true"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCheckBrokenShortImageInfo()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "broken-short-image-info.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "check",
      "--file",
      file.toAbsolutePath().toString(),
      "--warnings-as-errors",
      "true"
    });
    assertEquals(1, r);
  }

  @Test
  public void testCheckBasic()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "basic.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "check",
      "--file",
      file.toAbsolutePath().toString(),
      "--warnings-as-errors",
      "true"
    });
    assertEquals(0, r);
  }

  @Test
  public void testCheckBasicLZ4()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "basic-lz4.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "check",
      "--file",
      file.toAbsolutePath().toString(),
      "--warnings-as-errors",
      "true"
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowMetadataBasic()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "basic.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-metadata",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(0, r);
  }

  @Test
  public void testShowMetadataEmpty()
    throws IOException
  {
    final var file =
      CLNTestDirectories.resourceOf(
        CLN1ParsersContract.class,
        this.directory,
        "empty.ctf"
      );

    final var r = CLNMain.mainExitless(new String[]{
      "show-metadata",
      "--file",
      file.toAbsolutePath().toString()
    });
    assertEquals(1, r);
  }
}
