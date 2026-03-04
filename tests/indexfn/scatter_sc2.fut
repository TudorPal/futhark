-- tests/indexfn/scatter_sc2.fut
-- Conditional scatter with an out-of-bounds branch, without array literals.

def f (m: {i64 | \m -> Range m (1, inf)})
      (conds: [m]bool)
      (xs:    [m]i64)
    : {[]i64 | \_ -> true} =
  let tflgs = map (\c -> if c then 1i64 else 0i64) conds
  let inds  = scan (+) 0i64 tflgs
  let total = inds[m-1] + tflgs[m-1]
  let is    = map2 (\c i -> if c then i else total) conds inds
  let out   = scatter (replicate total 0i64) is xs
  in out