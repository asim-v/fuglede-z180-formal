# Building the article

The article uses a clean two-column LaTeX layout and is written as a
single-author paper.

On Windows:

```powershell
.\paper\build.ps1
```

The equivalent commands on any system with a conventional TeX distribution
are:

```bash
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The committed `main.pdf` is the rendered publication artifact.

The bibliography is stored in `references.bib`. The article uses an
expository single-author voice; author and affiliation metadata are set near
the beginning of `main.tex` and in `../CITATION.cff`.
