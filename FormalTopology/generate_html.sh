#!/bin/bash

echo "Running Agda..."

agda --safe --html --html-highlight=auto Main.lagda.md

cp -f ../resources/Agda.css html/Agda.css

cd html

for f in `ls *.md`; do
    echo "Compiling Markdown: $f..."
    pandoc $f --css Agda.css -o "$(basename --suffix='.md' $f).html"
done
