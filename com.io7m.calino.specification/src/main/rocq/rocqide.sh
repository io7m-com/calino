#!/bin/sh

ROCQ_MAPPINGS=""
ROCQ_MAPPINGS="${ROCQ_MAPPINGS} -Q Calino com.io7m.calino"
ROCQ_MAPPINGS="${ROCQ_MAPPINGS} -Q roctetorder/src/main/rocq com.io7m.octetorder"
ROCQ_MAPPINGS="${ROCQ_MAPPINGS} -Q rentomos/src/main/rocq com.io7m.entomos"

exec rocqide ${ROCQ_MAPPINGS} "$@"
