// Optional verification only; this script is never copied into the generated site.
const fs = require('fs');
const path = require('path');
const {pathToFileURL} = require('url');
let chromium;
try {
  ({chromium} = require('playwright'));
} catch {
  console.log('Playwright unavailable: mobile render skipped');
  process.exit(77);
}

(async () => {
  const [output, slug, saved] = process.argv.slice(2);
  let browser;
  try {
    browser = await chromium.launch({headless: true});
  } catch {
    console.log('Chromium unavailable: mobile render skipped');
    process.exit(77);
  }
  fs.mkdirSync(saved, {recursive: true});
  const results = [];
  try {
    for (const colorScheme of ['light', 'dark']) {
      const context = await browser.newContext({viewport: {width: 375, height: 812},
        deviceScaleFactor: 1, isMobile: true, hasTouch: true, colorScheme});
      for (const [name, relative] of [['index', 'index.html'], ['paper', `papers/${slug}/index.html`]]) {
        const page = await context.newPage();
        await page.goto(pathToFileURL(path.join(output, relative)).href);
        await page.evaluate(() => document.fonts.ready);
        const metrics = await page.evaluate(() => ({
          viewport: innerWidth,
          scrollWidth: document.documentElement.scrollWidth,
          bodyWidth: document.body.scrollWidth,
          font: getComputedStyle(document.body).fontSize,
          textAdjust: getComputedStyle(document.documentElement).webkitTextSizeAdjust,
          minTapHeight: Math.min(...Array.from(document.querySelectorAll('a'), a => a.getBoundingClientRect().height)),
          horizontalElements: Array.from(document.querySelectorAll('body *')).filter(el =>
            el.getBoundingClientRect().right > innerWidth + 1 || el.getBoundingClientRect().left < -1).length
        }));
        if (metrics.viewport !== 375 || metrics.scrollWidth > 375 || metrics.bodyWidth > 375 ||
            metrics.horizontalElements || metrics.minTapHeight < 44 || metrics.font !== '17px' ||
            metrics.textAdjust !== '100%') {
          throw new Error(`Mobile layout failed for ${name}/${colorScheme}: ${JSON.stringify(metrics)}`);
        }
        const filename = `${name}-375-${colorScheme}.png`;
        await page.screenshot({path: path.join(saved, filename), fullPage: name === 'paper'});
        results.push({page: name, slug: name === 'paper' ? slug : null, colorScheme,
          screenshot: filename, ...metrics});
        await page.close();
      }
      await context.close();
    }
    fs.writeFileSync(path.join(saved, 'metrics.json'), JSON.stringify(results, null, 2) + '\n');
    console.log('Mobile PASS: 375px, light/dark, no overflow, 17px text, tap heights >=44px; ' +
      results.map(result => result.screenshot).join(', '));
  } finally {
    await browser.close();
  }
})().catch(error => {console.error(error.message); process.exitCode = 1;});
