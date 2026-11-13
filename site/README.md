Build and check the paper site with Python 3.9+, Node.js 22+ and `pdftotext`:

```sh
npm ci --prefix site --ignore-scripts --no-audit --no-fund
python3 -m unittest discover -s site -p 'test_*.py'
python3 site/build.py . _site --base-url https://clanklab.org/
python3 site/check.py _site --base-url https://clanklab.org/
```

The output directory must be empty. The build reads public Zenodo metadata
and verifies the adjacent PDFs against its checksums.

Math is rendered to native MathML at build time using KaTeX 0.19.0,
pinned by the npm lockfile. Inline `$…$` and `\(…\)`, and display `$$…$$`
and `\[…\]`, are supported in visible titles and abstracts. Use `\$` for a
literal dollar; unmatched dollars and
currency such as `$5 or $10` are left as text. Whitespace immediately inside
single dollars, or a digit immediately after the closing dollar, prevents
them from being treated as math. Invalid TeX fails the build.

The browser renders MathML with its own math fonts. The generated pages
need no KaTeX scripts, stylesheets, fonts, or third-party requests and work
with JavaScript disabled. MathML provides accessible formulas. Document
titles and Highwire `citation_*` metadata retain their original plain text,
including TeX.
The checker rejects raw math in visible text, HTML in citation metadata,
and unexpected scripts, stylesheets or other assets. See
`vendor/katex/README.md` for the dependency and license.
