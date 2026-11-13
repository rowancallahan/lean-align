// node Testing/wasm/browser_test.js URL worker|page [chromium flags...]   (page = on the page thread, test only)
// URL serves worker.js, index.html, lean-align.{js,wasm} and data/{genome.fa,idx1,idx1.chromosomes,r1.fq,r2.fq}.
// Prints one JSON line per job (build, then map). Fails on any page error.
const { chromium } = require('playwright');
(async () => {
  const [url, where, ...flags] = process.argv.slice(2);
  if (where !== 'worker' && where !== 'page') throw new Error('worker|page');
  const b = await chromium.launch({ args: flags });
  const p = await b.newPage();
  p.on('pageerror', (e) => { throw e; });
  await p.goto(url + '/index.html');
  console.log(JSON.stringify({ crossOriginIsolated: await p.evaluate(() => crossOriginIsolated), where, flags }));
  const jobs = [
    { args: ['build', '/genome.fa', '/idx'], inputs: { '/genome.fa': 'data/genome.fa' }, outputs: ['/idx', '/idx.chromosomes'] },
    { args: ['map', '/idx1', '/r1.fq', '/r2.fq', '/out.sam', '100', '1000'],
      inputs: { '/idx1': 'data/idx1', '/idx1.chromosomes': 'data/idx1.chromosomes', '/r1.fq': 'data/r1.fq', '/r2.fq': 'data/r2.fq' },
      outputs: ['/out.sam'] },
  ];
  for (const j of jobs) {
    const r = await p.evaluate(([j, where]) => (where === 'worker' ? run(j) : runJob(j)), [j, where]);
    console.log(JSON.stringify({ job: j.args[0], ...r }));
  }
  await b.close();
})();
