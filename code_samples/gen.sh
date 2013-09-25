#!/bin/sh
SRC=~/Code/mezzo/src
LIST=interesting-tests
TOTAL=$(wc -l $LIST | awk '{print $1}')
I=1

echo "Generating $TOTAL HTML files."

function gen_file_if () {
  if [ -f $SRC/$1 ]; then
    echo -ne "\r$I/$TOTAL $1"
    I=$(($I + 1))
    vim -gf $SRC/$1 -c ":colorscheme wombat" -c ":TOhtml" -c ":w!" -c ":qa"
    \mv $SRC/$1.html .
  fi
}

for f in $(cat $LIST); do
  # .mz
  gen_file_if $f;
  # .mzi, does nothing if the file is already .mzi
  gen_file_if "$f"i;
done
