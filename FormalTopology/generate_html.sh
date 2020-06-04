#!/bin/bash

agda --safe Main.lagda.md

for f in `ls *.lagda.md`; do
    agda --html --html-highlight=auto $f
done

for f in `ls *.agda`; do
    agda --html $f
done

cp -f ../resources/Agda.css html/Agda.css

cd html

for f in `ls *.md`; do
    pandoc $f --css Agda.css -o "$(basename --suffix='.md' $f).html"
done
