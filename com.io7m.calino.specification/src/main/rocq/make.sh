#!/bin/sh -ex

ROCQ_MAPPINGS=""
ROCQ_MAPPINGS="${ROCQ_MAPPINGS} -Q Calino com.io7m.calino"
ROCQ_MAPPINGS="${ROCQ_MAPPINGS} -Q roctetorder/src/main/rocq com.io7m.octetorder"
ROCQ_MAPPINGS="${ROCQ_MAPPINGS} -Q rentomos/src/main/rocq com.io7m.entomos"

rocq compile ${ROCQ_MAPPINGS} roctetorder/src/main/rocq/OctetOrder.v

rocq compile ${ROCQ_MAPPINGS} rentomos/src/main/rocq/Alignment.v
rocq compile ${ROCQ_MAPPINGS} rentomos/src/main/rocq/Divisible.v
rocq compile ${ROCQ_MAPPINGS} rentomos/src/main/rocq/Binary.v
rocq compile ${ROCQ_MAPPINGS} rentomos/src/main/rocq/Tags.v
rocq compile ${ROCQ_MAPPINGS} rentomos/src/main/rocq/FileFormat.v
rocq compile ${ROCQ_MAPPINGS} rentomos/src/main/rocq/ExampleFileFormat.v

rocq compile ${ROCQ_MAPPINGS} Calino/StringUtility.v
rocq compile ${ROCQ_MAPPINGS} Calino/Metadata.v
rocq compile ${ROCQ_MAPPINGS} Calino/Descriptor.v
rocq compile ${ROCQ_MAPPINGS} Calino/ChannelSemantic.v
rocq compile ${ROCQ_MAPPINGS} Calino/ChannelDescription.v
rocq compile ${ROCQ_MAPPINGS} Calino/ChannelType.v
rocq compile ${ROCQ_MAPPINGS} Calino/StandardFormats.v
rocq compile ${ROCQ_MAPPINGS} Calino/Compression.v
rocq compile ${ROCQ_MAPPINGS} Calino/SuperCompression.v
rocq compile ${ROCQ_MAPPINGS} Calino/ColorSpace.v
rocq compile ${ROCQ_MAPPINGS} Calino/Flag.v
rocq compile ${ROCQ_MAPPINGS} Calino/CoordinateSystem.v
rocq compile ${ROCQ_MAPPINGS} Calino/ImageSize.v
rocq compile ${ROCQ_MAPPINGS} Calino/ImageInfo.v
rocq compile ${ROCQ_MAPPINGS} Calino/CubeMipMap.v
rocq compile ${ROCQ_MAPPINGS} Calino/MipMap.v
rocq compile ${ROCQ_MAPPINGS} Calino/ArrayMipMap.v
rocq compile ${ROCQ_MAPPINGS} Calino/ThreeDMipMap.v
rocq compile ${ROCQ_MAPPINGS} Calino/Texture.v
rocq compile ${ROCQ_MAPPINGS} Calino/Binary.v

mkdir -p html

coqdoc ${ROCQ_MAPPINGS} --utf8 -d html Calino/*.v
