// Tests for inc.fut.
//
// The goal is to check:
//   1. the backwards-compatible WASM API: newFutharkContext() + fc.inc(...)
//   2. the shared entry API: fc.entry.inc(...)
//   3. the preferred FutharkModule API: new FutharkModule() + await fut.init()

import assert from "assert/strict";

// Hack for running generated ES6 modules from Emscripten with Node.
// https://github.com/emscripten-core/emscripten/issues/11792#issuecomment-877120580
import { dirname } from "path";
import { createRequire } from "module";

// substring removes file:// from the filepath
globalThis.__dirname = dirname(import.meta.url).substring(7);
globalThis.require = createRequire(import.meta.url);

// Imports from the generated ES6 module.
import { newFutharkContext, FutharkContext, FutharkModule } from "./build/inc/inc.mjs";

async function main() {
  console.log();
  console.log("Testing inc.fut");
  console.log();

  console.log("Testing backwards-compatible WASM API: newFutharkContext + fc.inc");

  const fc = await newFutharkContext();

  assert.ok(fc instanceof FutharkContext, "newFutharkContext should return a FutharkContext");
  assert.ok(fc instanceof FutharkModule, "FutharkContext should extend FutharkModule");

  const old_api_res = fc.inc(9);
  assert.equal(old_api_res, 10);

  console.log("backwards-compatible direct API ok");

  console.log("Testing shared entry API on FutharkContext: fc.entry.inc");

  assert.ok(fc.entry, "fc.entry should exist");
  assert.equal(typeof fc.entry.inc, "function");

  const entry_api_res = await fc.entry.inc(9);
  assert.equal(entry_api_res, 10);

  console.log("FutharkContext entry API ok");

  fc.free();

  console.log("Testing preferred FutharkModule API");

  const fut = new FutharkModule();

  assert.ok(fut instanceof FutharkModule, "fut should be a FutharkModule");

  await fut.init();

  assert.ok(fut.entry, "fut.entry should exist");
  assert.equal(typeof fut.entry.inc, "function");

  const module_api_res = await fut.entry.inc(9);
  assert.equal(module_api_res, 10);

  console.log("FutharkModule entry API ok");

  fut.free();

  console.log();
  console.log("inc tests complete");
  console.log();
}

main();