# Building the article

The article uses a standard two-column LaTeX layout.

With Tectonic:

```bash
cd paper
tectonic main.tex --keep-logs
```

With a conventional TeX distribution:

```bash
cd paper
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

The committed `main.pdf` is the rendered publication artifact.

