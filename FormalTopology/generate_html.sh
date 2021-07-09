#!/bin/bash

echo "Running Agda..."

agda --safe --html --html-highlight=auto Main.lagda.md

cp -f ../resources/Agda.css html/Agda.css

cd html

for f in `ls *.md`; do
    echo "Compiling Markdown: $f..."
    if [ $f == "FrameOfNuclei.md" ]; then
        echo "Handling the FrameOfNuclei module..."
        pandoc $f --css Agda.css --toc -o "$(basename --suffix='.md' $f).html"
    else
        pandoc $f -s --css Agda.css --toc -o "$(basename --suffix='.md' $f).html"
    fi
done
