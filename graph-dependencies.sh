#!/bin/bash
set -x

cargo deps 2> /dev/null > dependencies.dot \
  && dot -Tpng dependencies.dot > dependencies.png \
  && feh dependencies.png

exit
