#!/bin/sh
rm -f index.html
touch index.html
for a in $(ls data/* | sort -V); do
  echo "<a href=\"viewer.html?json_file=$a\">$a</a><br>" >> index.html
done
