// Tests for inc.fut.
//
// The goal is to check both:
//   1. the original WASM API: fc.inc(...)
//   2. the new WebGPU-style entry API: fc.entry.inc(...)

import assert from 'assert/strict';

// Hack for running generated ES6 modules from Emscripten with Node.
// https://github.com/emscripten-core/emscripten/issues/11792#issuecomment-877120580
import { dirname } from "path";
import { createRequire } from "module";

// substring removes file:// from the filepath
globalThis.__dirname = dirname(import.meta.url).substring(7);
globalThis.require = createRequire(import.meta.url);

// Imports from the generated ES6 module.
import { newFutharkContext } from "./build/inc/inc.mjs";

newFutharkContext().then(fc => {
  console.log();
  console.log("Testing inc.fut");
  console.log();

  console.log("Testing original WASM entry point API: fc.inc");

  const old_api_res = fc.inc(9);
  assert.equal(old_api_res, 10);

  console.log("original API ok");

  console.log("Testing WebGPU-style entry API: fc.entry.inc");

  assert.ok(fc.entry, "fc.entry should exist");
  assert.equal(typeof fc.entry.inc, "function");

  const new_api_res = fc.entry.inc(9);
  assert.equal(new_api_res, 10);

  console.log("entry API ok");

  fc.free();

  console.log();
  console.log("inc tests complete");
  console.log();
});