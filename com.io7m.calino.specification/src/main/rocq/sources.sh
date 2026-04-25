#!/bin/sh

for f in $(find . -type f -name '*.v' | sort -u | sed 's/\.\///g')
do
  ID=$(uuidgen -s -n @x500 -N "$f")

  cat <<EOF
  <FormalItem title="$f" id="${ID}">
    <Verbatim><xi:include href="$f" parse="text"/></Verbatim>
  </FormalItem>
EOF
done
