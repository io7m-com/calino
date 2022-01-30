#!/bin/sh -ex

coqc -Q Calino Calino Calino/Alignment.v
coqc -Q Calino Calino Calino/StringUtility.v
coqc -Q Calino Calino Calino/Divisible8.v
coqc -Q Calino Calino Calino/Metadata.v
coqc -Q Calino Calino Calino/Descriptor.v
coqc -Q Calino Calino Calino/ChannelSemantic.v
coqc -Q Calino Calino Calino/ChannelDescription.v
coqc -Q Calino Calino Calino/ChannelType.v
coqc -Q Calino Calino Calino/Compression.v
coqc -Q Calino Calino Calino/SuperCompression.v
coqc -Q Calino Calino Calino/ColorSpace.v
coqc -Q Calino Calino Calino/ByteOrder.v
coqc -Q Calino Calino Calino/Flag.v
coqc -Q Calino Calino Calino/CoordinateSystem.v
coqc -Q Calino Calino Calino/ImageSize.v
coqc -Q Calino Calino Calino/ImageInfo.v
coqc -Q Calino Calino Calino/MipMap.v
coqc -Q Calino Calino Calino/Image.v
coqc -Q Calino Calino Calino/Binary.v

mkdir -p html

coqdoc -Q Calino Calino --utf8 -d html Calino/*.v
