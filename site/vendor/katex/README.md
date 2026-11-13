KaTeX 0.19.0 is used only by the build, through the exact dependency and
integrity recorded in `../../package-lock.json`. Its official npm release is:
https://registry.npmjs.org/katex/-/katex-0.19.0.tgz

The unmodified MIT license from that release is included in `LICENSE`.

Node.js renders TeX to MathML during the build. No KaTeX JavaScript,
stylesheets or fonts are copied to the generated site; readers use their
browser's native MathML rendering without third-party requests.
