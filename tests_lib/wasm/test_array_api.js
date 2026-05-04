// Tests for array_api.fut.
//
// This checks both:
//   1. the old WASM array constructor API
//   2. the new WebGPU-style array constructor API

import assert from "assert/strict";

import { dirname } from "path";
import { createRequire } from "module";

globalThis.__dirname = dirname(import.meta.url).substring(7);
globalThis.require = createRequire(import.meta.url);

import { newFutharkContext } from "./build/array_api/array_api.mjs";

newFutharkContext().then(async fc => {
  console.log();
  console.log("Testing array_api.fut");
  console.log();

  console.log("Testing original WASM 1D array constructor API");

  const xs_i32 = new Int32Array([1, 2, 3, 4, 5]);
  const fut_xs_i32_old = fc.new_i32_1d(xs_i32, xs_i32.length);

  const old_sum_i32 = fc.sum_i32_1d(fut_xs_i32_old);
  assert.equal(old_sum_i32, 15);

  console.log("old 1D constructor API ok");

  console.log("Testing WebGPU-style 1D array constructor API");

  assert.ok(fc.i32_1d, "fc.i32_1d should exist");
  assert.equal(typeof fc.i32_1d.from_data, "function");

  const fut_xs_i32_new = fc.i32_1d.from_data(xs_i32, xs_i32.length);

  const new_sum_i32 = fc.entry.sum_i32_1d(fut_xs_i32_new);
  assert.equal(new_sum_i32, 15);

  console.log("new 1D constructor API ok");

  console.log("Testing WebGPU-style 1D from_jsarray API");

  assert.equal(typeof fc.i32_1d.from_jsarray, "function");

  const fut_xs_i32_jsarray = fc.i32_1d.from_jsarray([1, 2, 3, 4, 5]);

  const jsarray_sum_i32 = fc.entry.sum_i32_1d(fut_xs_i32_jsarray);
  assert.equal(jsarray_sum_i32, 15);

  console.log("new 1D from_jsarray API ok");

  console.log("Testing original WASM 2D array constructor API");

  const xs_i64 = new BigInt64Array([1n, 2n, 3n, 4n, 5n, 6n]);
  const fut_xs_i64_old = fc.new_i64_2d(xs_i64, 2, 3);

  const old_sum_i64 = fc.sum_i64_2d(fut_xs_i64_old);
  assert.equal(old_sum_i64, 21n);

  console.log("old 2D constructor API ok");

  console.log("Testing WebGPU-style 2D array constructor API");

  assert.ok(fc.i64_2d, "fc.i64_2d should exist");
  assert.equal(typeof fc.i64_2d.from_data, "function");

  const fut_xs_i64_new = fc.i64_2d.from_data(xs_i64, 2, 3);

  const new_sum_i64 = fc.entry.sum_i64_2d(fut_xs_i64_new);
  assert.equal(new_sum_i64, 21n);

  console.log("new 2D constructor API ok");

  console.log("Testing returned arrays still work with old API");

  const fut_replicated_1d = fc.entry.replicate_f32_1d(4n, 1.5);
  const replicated_1d = fut_replicated_1d.toArray();

  assert.equal(replicated_1d.length, 4);
  for (let i = 0; i < replicated_1d.length; i++) {
    assert.ok(Math.abs(replicated_1d[i] - 1.5) < 0.0001);
  }

  const fut_replicated_2d = fc.entry.replicate_f32_2d(2n, 3n, 2.5);
  const replicated_2d = fut_replicated_2d.toArray();

  assert.equal(replicated_2d.length, 2);
  assert.equal(replicated_2d[0].length, 3);

  for (let i = 0; i < replicated_2d.length; i++) {
    for (let j = 0; j < replicated_2d[i].length; j++) {
      assert.ok(Math.abs(replicated_2d[i][j] - 2.5) < 0.0001);
    }
  }

  console.log("returned arrays ok");
  
  fut_xs_i32_old.free();
  fut_xs_i32_new.free();
  fut_xs_i32_jsarray.free();
  fut_xs_i64_old.free();
  fut_xs_i64_new.free();
  fut_replicated_1d.free();
  fut_replicated_2d.free();

  console.log("Testing WebGPU-style returned array methods");

  const fut_values_arr = fc.entry.replicate_f32_1d(3n, 4.5);

  assert.equal(typeof fut_values_arr.values, "function");
  assert.equal(typeof fut_values_arr.get_shape, "function");
  
  const values = await fut_values_arr.values();
  const shape = fut_values_arr.get_shape();
  
  assert.ok(values instanceof Float32Array);
  assert.ok(shape instanceof BigInt64Array);
  
  assert.equal(shape.length, 1);
  assert.equal(shape[0], 3n);
  
  assert.equal(values.length, 3);
  for (let i = 0; i < values.length; i++) {
    assert.ok(Math.abs(values[i] - 4.5) < 0.0001);
  }

  console.log("WebGPU-style returned array methods ok");

  fut_values_arr.free();

  fc.free();

  console.log();
  console.log("array_api tests complete");
  console.log();
});