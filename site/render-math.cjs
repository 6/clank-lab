// Build-time only. No JavaScript is shipped to readers.
const fs = require('node:fs');
const katex = require('katex');

try {
  const expressions = JSON.parse(fs.readFileSync(0, 'utf8'));
  const rendered = expressions.map(({tex, display}) => katex.renderToString(tex, {
    displayMode: display,
    output: 'mathml',
    throwOnError: true,
    trust: false,
    strict: 'error',
    maxExpand: 1000,
  }));
  process.stdout.write(JSON.stringify(rendered));
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}
