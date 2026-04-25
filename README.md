calino
===

[![Maven Central](https://img.shields.io/maven-central/v/com.io7m.calino/com.io7m.calino.svg?style=flat-square)](http://search.maven.org/#search%7Cga%7C1%7Cg%3A%22com.io7m.calino%22)
[![Maven Central (snapshot)](https://img.shields.io/maven-metadata/v?metadataUrl=https%3A%2F%2Fcentral.sonatype.com%2Frepository%2Fmaven-snapshots%2Fcom%2Fio7m%2Fcalino%2Fcom.io7m.calino%2Fmaven-metadata.xml&style=flat-square)](https://central.sonatype.com/repository/maven-snapshots/com/io7m/calino/)
[![Codecov](https://img.shields.io/codecov/c/github/io7m-com/calino.svg?style=flat-square)](https://codecov.io/gh/io7m-com/calino)
![Java Version](https://img.shields.io/badge/25-java?label=java&color=5ce67e)

![com.io7m.calino](./src/site/resources/calino.jpg?raw=true)

| JVM | Platform | Status |
|-----|----------|--------|
| OpenJDK (Temurin) Current | Linux | [![Build (OpenJDK (Temurin) Current, Linux)](https://img.shields.io/github/actions/workflow/status/io7m-com/calino/main.linux.temurin.current.yml)](https://www.github.com/io7m-com/calino/actions?query=workflow%3Amain.linux.temurin.current)|
| OpenJDK (Temurin) LTS | Linux | [![Build (OpenJDK (Temurin) LTS, Linux)](https://img.shields.io/github/actions/workflow/status/io7m-com/calino/main.linux.temurin.lts.yml)](https://www.github.com/io7m-com/calino/actions?query=workflow%3Amain.linux.temurin.lts)|
| OpenJDK (Temurin) Current | Windows | [![Build (OpenJDK (Temurin) Current, Windows)](https://img.shields.io/github/actions/workflow/status/io7m-com/calino/main.windows.temurin.current.yml)](https://www.github.com/io7m-com/calino/actions?query=workflow%3Amain.windows.temurin.current)|
| OpenJDK (Temurin) LTS | Windows | [![Build (OpenJDK (Temurin) LTS, Windows)](https://img.shields.io/github/actions/workflow/status/io7m-com/calino/main.windows.temurin.lts.yml)](https://www.github.com/io7m-com/calino/actions?query=workflow%3Amain.windows.temurin.lts)|

## calino

A strongly-specified file format for textures.

## Features

* Strongly specified file format with full formal specification and proofs
  of specification properties.
* Supports the storage and retrieval of 2D, cube, and array textures.
* Supports LZ4 and DEFLATE compression of image data.
* Command-line tools and API for image manipulation.
* An extensive automated test suite with high coverage.
* Written in pure Java 25.
* [OSGi-ready](https://www.osgi.org/).
* [JPMS-ready](https://en.wikipedia.org/wiki/Java_Platform_Module_System).
* ISC license.

## Usage

See the [documentation and specification](https://www.io7m.com/software/calino/).

