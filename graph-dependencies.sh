#!/bin/bash
set -x

cargo graph > dependencies.dot && dot -Tpng dependencies.dot > dependencies.png \
  && feh dependencies.png

exit
