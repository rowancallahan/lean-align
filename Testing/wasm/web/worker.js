// Runs lean-align (single-threaded wasm) on MEMFS. job = {args, inputs: {path: url}, outputs: [path]}.
// Returns {code, sha256: {path: hex}, size: {path: n}, memMB, ms}. No error recovery: any failure surfaces as an error.
// In a Web Worker: one job per message. On the page (test only): call runJob directly.
async function runJob({ args, inputs, outputs }) {
  const M = await LeanAlign({ noExitRuntime: false });
  for (const [p, url] of Object.entries(inputs)) {
    const r = await fetch(url);
    if (!r.ok) throw new Error(url + ' ' + r.status);
    M.FS.writeFile(p, new Uint8Array(await r.arrayBuffer()));
  }
  const t = performance.now();
  let code = 0;
  try { M.callMain(args); } catch (x) { if (!(x && x.name === 'ExitStatus')) throw x; code = x.status; }
  const ms = performance.now() - t;
  const sha256 = {}, size = {};
  for (const p of outputs) {
    const b = M.FS.readFile(p);
    size[p] = b.length;
    sha256[p] = [...new Uint8Array(await crypto.subtle.digest('SHA-256', b))].map(x => x.toString(16).padStart(2, '0')).join('');
  }
  return { code, sha256, size, memMB: Math.round(M.HEAP8.buffer.byteLength / 2 ** 20), ms: Math.round(ms) };
}
if (typeof WorkerGlobalScope !== 'undefined') {
  importScripts('lean-align.js');
  onmessage = async (e) => postMessage(await runJob(e.data));
}
