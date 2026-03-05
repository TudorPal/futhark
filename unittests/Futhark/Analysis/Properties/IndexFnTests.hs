module Futhark.Analysis.Properties.IndexFnTests (tests) where

import Control.Monad (forM, forM_, unless, when)
import Data.Maybe (mapMaybe)
import Futhark.Analysis.Properties.Substitute (propFlattenOnce)
import Futhark.Analysis.Properties.Convert
import Futhark.Analysis.Properties.IndexFn
import Futhark.Analysis.Properties.IndexFnPlus (subIndexFn)
import Futhark.Analysis.Properties.Monad
-- import Futhark.Analysis.Properties.Property (Predicate (..), Property (..))
import Futhark.Analysis.Properties.Symbol (Symbol (..), neg)
import Futhark.Analysis.Properties.Unify (renameSame, unify)
import Futhark.Compiler.CLI (fileProg, readProgramOrDie)
import Futhark.MonadFreshNames (newNameFromString)
import Futhark.SoP.SoP (int2SoP, sym2SoP, (.*.), (.+.), (.-.))
import Futhark.Util.Pretty (Pretty, docStringW, line, pretty, (<+>))
import Language.Futhark qualified as E
import Test.Tasty
import Test.Tasty.HUnit

(@??=) :: (Eq a, Pretty a) => a -> a -> IO ()
actual @??= expected =
  unless (actual == expected) (assertFailure msg)
  where
    msg =
      docStringW 120 $
        "expected:" <+> pretty expected <> line <> "but got: " <+> pretty actual

-- helper functions to help in Cat removal tests
hasCat :: IndexFn -> Bool
hasCat = any (any isCatQ) . shape
  where
    isCatQ (Forall _ d) = isCat d
    isCat (Cat {}) = True
    isCat _ = False

hasFlattenedDim :: IndexFn -> Bool
hasFlattenedDim = any ((> 1) . length) . shape

data CatExpectation = AllowCat | NoCat
  deriving (Eq, Show)

tests :: TestTree
tests =
  testGroup "Properties.IndexFn"
    [ programTests
    , propFlattenTests
    , catRefactorTests
    ]

catRefactorTests :: TestTree
catRefactorTests =
  testGroup "CatRefactor"
    [ scatterSc2RuleTest NoCat
    , noCatSelectedProgramsTest
    --, noCatPrograms
    ]

noCatPrograms :: TestTree
noCatPrograms =
  testGroup
    "NoCatPrograms"
    [ mkNoCatTest "tests/indexfn/fft.fut"
    , mkNoCatTest "tests/indexfn/bug.fut"
    -- , mkNoCatTest "tests/indexfn/bug2.fut"
    , mkNoCatTest "tests/indexfn/map.fut"
    , mkNoCatTest "tests/indexfn/scatter_perm.fut"
    , mkNoCatTest "tests/indexfn/reverse.fut"
    , mkNoCatTest "tests/indexfn/abs.fut"
    , mkNoCatTest "tests/indexfn/map-tuple.fut"
    , mkNoCatTest "tests/indexfn/map-tuple2.fut"
    , mkNoCatTest "tests/indexfn/map-if.fut"
    , mkNoCatTest "tests/indexfn/map-if-nested.fut"
    , mkNoCatTest "tests/indexfn/map-if-elim.fut"
    , mkNoCatTest "tests/indexfn/scalar.fut"
    , mkNoCatTest "tests/indexfn/scan.fut"
    , mkNoCatTest "tests/indexfn/scan_lambda.fut"
    , mkNoCatTest "tests/indexfn/scan2.fut"
    , mkNoCatTest "tests/indexfn/scalar2.fut"
    , mkNoCatTest "tests/indexfn/part2indices.fut"
    , mkNoCatTest "tests/indexfn/map2.fut"
    , mkNoCatTest "tests/indexfn/part2indices_numeric_conds.fut"
    , mkNoCatTest "tests/indexfn/part2indices_predicatefn.fut"
    , mkNoCatTest "tests/indexfn/part2indices_predicatefn2.fut"
    , mkNoCatTest "tests/indexfn/part3indices.fut"
    , mkNoCatTest "tests/indexfn/segment_sum.fut"
    , mkNoCatTest "tests/indexfn/filter_indices.fut"
    , mkNoCatTest "tests/indexfn/partition.fut"
    , mkNoCatTest "tests/indexfn/partition2_alt.fut"
    , mkNoCatTest "tests/indexfn/seg_partition.fut"
    , mkNoCatTest "tests/indexfn/partition3.fut"
    , mkNoCatTest "tests/indexfn/filter.fut"
    , mkNoCatTest "tests/indexfn/filter_segmented_array.fut"
    , mkNoCatTest "tests/indexfn/maxMatch.fut"
    , mkNoCatTest "tests/indexfn/maxMatch_2d.fut"
    , mkNoCatTest "tests/indexfn/kmeans_kernel.fut"
    , mkNoCatTest "tests/indexfn/nd_map-map.fut"
    , mkNoCatTest "tests/indexfn/nd_map-scan.fut"
    , mkNoCatTest "tests/indexfn/nd_expansion.fut"
    , mkNoCatTest "tests/indexfn/if-array-type.fut"
    , mkNoCatTest "tests/indexfn/zipArgs2d.fut"
    , mkNoCatTest "tests/indexfn/primes.fut"
    , mkNoCatTest "tests/indexfn/mis.fut"
    , mkNoCatTest "tests/indexfn/quickhull.fut"
    , mkNoCatTest "tests/indexfn/srad.fut"
    -- , mkNoCatTest "tests/indexfn/for_postcondition.fut"
    -- , mkNoCatTest "tests/indexfn/for_precondition.fut"
    -- , mkNoCatTest "tests/indexfn/for_parsing.fut"
    --, mkNoCatTest "tests/indexfn/scatter_sc2.fut"
    ]
  where
    mkNoCatTest programFile = testCase (basename programFile) $ do
      (_, imports, vns) <- readProgramOrDie programFile
      let last_import = case reverse imports of
            [] -> error "No imports"
            x : _ -> x
      let vbs = getValBinds last_import
      when (null vbs) $
        assertFailure "No value bindings found."

      let actuals =
            fst $ flip runIndexFnM vns $ do
              let preceding_vbs = init vbs
              let last_vb = last vbs
              forM_ preceding_vbs mkIndexFnValBind
              mkIndexFnValBind last_vb

      when (null actuals) $
        assertFailure "The last value binding does not create an index function."

      forM_ actuals $ \f -> do
        unless (not (hasCat f)) $
          assertFailure $ docStringW 120 $
            "Expected no Cat domains, but got:\n" <> pretty f

    basename = drop (length prefix)
      where
        prefix :: String
        prefix = "tests/indexfn/"

    getValBinds = mapMaybe getValBind . E.progDecs . fileProg . snd

    getValBind (E.ValDec vb) = Just vb
    getValBind _ = Nothing

noCatSelectedProgramsTest :: TestTree
noCatSelectedProgramsTest =
  testGroup "NoCatSelectedPrograms"
    [ mkNoCatProgram "tests/indexfn/mk_flag_array.fut"
    ]
  where
    mkNoCatProgram programFile =
      testCase (basename programFile) $ do
        (_, imports, vns) <- readProgramOrDie programFile
        let last_import = case reverse imports of
              [] -> error "No imports"
              x : _ -> x
        let vbs = getValBinds last_import
        when (null vbs) $
          assertFailure "No value bindings found."

        -- Same evaluation scheme as mkTest: run all preceding value bindings
        -- before constructing the last one (same VNameSource).
        let actuals =
              fst $ flip runIndexFnM vns $ do
                let preceding_vbs = init vbs
                let last_vb = last vbs
                forM_ preceding_vbs mkIndexFnValBind
                mkIndexFnValBind last_vb

        when (null actuals) $
          assertFailure "The last value binding does not create an index function."

        forM_ actuals $ \f -> do
          unless (not (hasCat f)) $
            assertFailure $ docStringW 120 $
              "Expected no Cat domains, but got:\n" <> pretty f

    basename = drop (length prefix)
      where
        prefix :: String
        prefix = "tests/indexfn/"

    getValBinds = mapMaybe getValBind . E.progDecs . fileProg . snd

    getValBind (E.ValDec vb) = Just vb
    getValBind _ = Nothing

scatterSc2RuleTest :: CatExpectation -> TestTree
scatterSc2RuleTest expect =
  testCase "Convert.scatterSc2 migration (direct rule)" $ do
    -- We just need a VNameSource to run IndexFnM. Any existing .fut is fine.
    (_, _, vns) <- readProgramOrDie "tests/indexfn/map.fut"

    let mf =
          fst $ flip runIndexFnM vns $ do
            -- size variable m (scalar)
            m <- newNameFromString "m"

            -- iterator names
            i <- newNameFromString "i"
            k <- newNameFromString "k"

            let mS = sym2SoP (Var m)

            -- xs : [0..m-1] -> i  (simple base array)
            let xs =
                  IndexFn
                    { shape = [[Forall i (Iota mS)]]
                    , body  = cases [(Bool True, sym2SoP (Var i))]
                    }

            -- vs : [0..m-1] -> k  (simple values array)
            let vs =
                  IndexFn
                    { shape = [[Forall k (Iota mS)]]
                    , body  = cases [(Bool True, sym2SoP (Var k))]
                    }

            -- is : shape [[k : Iota m]]
            --
            -- Two branches crafted to match scatterSc2's expected sorting:
            --   - Unknown for in-domain check: expression m (cannot prove m < m)
            --   - Yes for in-domain check: expression k (k is provably in [0,m))
            --
            -- The in-bounds branch uses e = k, which satisfies the monotonic
            -- boundary checks inside scatterSc2 (e[0]=0, e[m]=m, monotone).
            let is =
                  IndexFn
                    { shape = [[Forall k (Iota mS)]]
                    , body =
                        cases
                          [ (Bool True, sym2SoP (Var m)) -- OOB-ish => Unknown in_dom_xs
                          , (Bool True, sym2SoP (Var k)) -- in-bounds => Yes in_dom_xs
                          ]
                    }

            tryScatterSc2 xs is vs

    f <- case mf of
      Nothing -> assertFailure "tryScatterSc2 returned Nothing (scatterSc2 did not match)." >> error "unreachable"
      Just f  -> pure f

    case expect of
      AllowCat ->
        assertBool
          "Expected Cat encoding OR a flattened dimension encoding"
          (hasCat f || hasFlattenedDim f)
      NoCat -> do
        assertBool "Expected no Cat domains" (not (hasCat f))
        assertBool "Expected a flattened dimension encoding" (hasFlattenedDim f)



propFlattenTests :: TestTree
propFlattenTests =
  testGroup "PropFlatten"
    [ testCase "rectangular i1 := i2*e3 + i3" $ do
        -- We just need a VNameSource to run IndexFnM. Any existing .fut is fine.
        (_, _, vns) <- readProgramOrDie "tests/indexfn/map.fut"
        let (mg', expected, _i1) =
              fst $ flip runIndexFnM vns $ do
                i1 <- newNameFromString "i1"
                i2 <- newNameFromString "i2"
                i3 <- newNameFromString "i3"
                n  <- newNameFromString "n"
                m  <- newNameFromString "m"

                let e2 = sym2SoP (Var n) -- 
                let e3 = sym2SoP (Var m)
                let e1 = e2 .*. e3

                let g =
                      IndexFn
                        { shape = [[Forall i1 (Iota e1)]]
                        , body  = cases [(Bool True, sym2SoP (Var i1))]
                        }

                let f =
                      IndexFn
                        { shape = [[Forall i2 (Iota e2), Forall i3 (Iota e3)]]
                        , body  = cases [(Bool True, sym2SoP (Var i3))]
                        }

                mg' <- propFlattenOnce 0 g f

                let eRow = sym2SoP (Var i2) .*. e3

                let expected =
                      IndexFn
                        { shape = [[Forall i2 (Iota e2), Forall i3 (Iota e3)]]
                        , body  = cases [(Bool True, eRow .+. sym2SoP (Var i3))]
                        }

                pure (mg', expected, i1)

        actual <- case mg' of
          Nothing -> assertFailure "propFlattenOnce did not apply (got Nothing)" >> error "unreachable"
          Just g' -> pure g'

        actual @??= expected

    , testCase "segmented i1 := e[i2] + i3 (e3 == e[i2+1]-e[i2])" $ do
        (_, _, vns) <- readProgramOrDie "tests/indexfn/map.fut"
        let (mg', expected, _i1) =
              fst $ flip runIndexFnM vns $ do
                i1 <- newNameFromString "i1"
                i2 <- newNameFromString "i2"
                i3 <- newNameFromString "i3"
                m  <- newNameFromString "m"
                e  <- newNameFromString "e"

                let e2 = sym2SoP (Var m)
                let i2S = sym2SoP (Var i2)

                let eAt t = sym2SoP (Apply (Var e) [t])

                let e3 = eAt (i2S .+. int2SoP 1) .-. eAt i2S
                let e1 = eAt e2

                let g =
                      IndexFn
                        { shape = [[Forall i1 (Iota e1)]]
                        , body  = cases [(Bool True, sym2SoP (Var i1))]
                        }

                let f =
                      IndexFn
                        { shape = [[Forall i2 (Iota e2), Forall i3 (Iota e3)]]
                        , body  = cases [(Bool True, sym2SoP (Var i3))]
                        }

                mg' <- propFlattenOnce 0 g f

                let expected =
                      IndexFn
                        { shape = [[Forall i2 (Iota e2), Forall i3 (Iota e3)]]
                        , body  = cases [(Bool True, eAt i2S .+. sym2SoP (Var i3))]
                        }

                pure (mg', expected, i1)

        actual <- case mg' of
          Nothing -> assertFailure "propFlattenOnce did not apply (got Nothing)" >> error "unreachable"
          Just g' -> pure g'

        actual @??= expected
    ]

programTests :: TestTree
programTests =
  testGroup
    "Programs"
    [ mkTest
        "tests/indexfn/fft.fut"
        ( pure $ \(i, n, xs, _) ->
            -- Match anything; we test whether the intermediate analysis is OK.
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body = cases [(Bool True, sym2SoP $ Hole xs)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/bug.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body = cases [(Bool True, sym2SoP (Apply (Hole xs) [sVar i .+. int2SoP 1]) .-. sym2SoP (Apply (Hole xs) [sVar i]))]
                }
            ]
        ),
      -- mkTest
      --   "tests/indexfn/bug2.fut"
      --   ( pure $ \(i, n, xs, _) ->
      --       [ IndexFn
      --           { shape = [[Forall i (Iota (sHole n))]],
      --             body = cases [(Bool True, sym2SoP $ Hole xs)]
      --           }
      --       ]
      --   ),
      mkTest
        "tests/indexfn/map.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body = cases [(Bool True, int2SoP 2 .*. sym2SoP (Apply (Hole xs) [sHole i]))]
                }
            ]
        ),
      mkTest
        "tests/indexfn/scatter_perm.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases
                      [(Bool True, sym2SoP $ Apply (Hole xs) [sHole i])]
                }
            ]
        ),
      mkTest
        "tests/indexfn/reverse.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases
                      [(Bool True, sym2SoP $ Apply (Hole xs) [sHole i])]
                }
            ]
        ),
      mkTest
        "tests/indexfn/abs.fut"
        ( pure $ \(_, _, x, _) ->
            [ IndexFn
                { shape = [],
                  body =
                    cases
                      [ (sHole x :< int2SoP 0, int2SoP (-1) .*. sHole x),
                        (sHole x :>= int2SoP 0, sHole x)
                      ]
                }
            ]
        ),
      mkTest
        "tests/indexfn/map-tuple.fut"
        ( pure $ \(i, n, xs, ys) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body = cases [(Bool True, int2SoP 2 .+. sym2SoP (Apply (Hole xs) [sHole i]))]
                },
              IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body = cases [(Bool True, int2SoP 3 .+. sym2SoP (Apply (Hole ys) [sHole i]))]
                }
            ]
        ),
      mkTest
        "tests/indexfn/map-tuple2.fut"
        ( pure $ \(i, n, xs, ys) ->
            let xs_i = sym2SoP $ Apply (Hole xs) [sHole i]
                ys_i = sym2SoP $ Apply (Hole ys) [sHole i]
             in [ IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body = cases [(Bool True, xs_i .*. ys_i)]
                    },
                  IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body = cases [(Bool True, xs_i .+. ys_i)]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/map-if.fut"
        ( pure $ \(i, n, xs, _) ->
            let xs_i = sym2SoP (Apply (Hole xs) [sHole i])
             in [ IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body =
                        cases
                          [ (xs_i :> int2SoP 100, int2SoP 2 .*. xs_i),
                            (xs_i :<= int2SoP 100, xs_i)
                          ]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/map-if-nested.fut"
        ( pure $ \(i, n, xs, _) ->
            let xs_i = sym2SoP (Apply (Hole xs) [sHole i])
             in [ IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body =
                        cases
                          [ (xs_i :> int2SoP 100, int2SoP 2 .*. xs_i),
                            (xs_i :<= int2SoP 100, xs_i)
                          ]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/map-if-elim.fut"
        ( pure $ \(i, n, xs, _) ->
            let xs_i = sym2SoP (Apply (Hole xs) [sHole i])
             in [ IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body = cases [(Bool True, int2SoP 2 .*. xs_i)]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/scalar.fut"
        ( pure $ \(i, _, x, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole x))]],
                  body = cases [(Bool True, int2SoP 2 .*. sHole x)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/scan.fut"
        ( pure $ \(i, n, xs, j) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases
                      [ ( Bool True,
                          sym2SoP $
                            Sum j (int2SoP 0) (sHole i) (Apply (Hole xs) [sHole j])
                        )
                      ]
                }
            ]
        ),
      mkTest
        "tests/indexfn/scan_lambda.fut"
        ( pure $ \(i, n, xs, j) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases
                      [ ( Bool True,
                          sym2SoP $
                            Sum j (int2SoP 0) (sHole i) (Apply (Hole xs) [sHole j])
                        )
                      ]
                }
            ]
        ),
      mkTest
        "tests/indexfn/scan2.fut"
        ( pure $ \(i, n, xs, j) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases
                      [ ( Bool True,
                          int2SoP 1 .+. sHole i .-. sym2SoP (Sum j (int2SoP 0) (sHole i) (Apply (Hole xs) [sHole j]))
                        )
                      ]
                }
            ]
        ),
      mkTest
        "tests/indexfn/scalar2.fut"
        ( pure $ \(_, n, xs, j) ->
            [ IndexFn
                { shape = [],
                  body =
                    cases
                      [ ( Bool True,
                          sym2SoP $
                            Sum j (int2SoP 0) (sHole n .-. int2SoP 1) (Apply (Hole xs) [sHole j])
                        )
                      ]
                }
            ]
        ),
      mkTest
        "tests/indexfn/part2indices.fut"
        ( pure $ \(i, n, xs, j) ->
            let xs_i = Apply (Hole xs) [sHole i]
             in [ IndexFn
                    { shape = [],
                      body =
                        cases
                          [ ( Bool True,
                              sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) (Apply (Hole xs) [sHole j]))
                            )
                          ]
                    },
                  IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body =
                        cases
                          [ ( xs_i,
                              sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) (Apply (Hole xs) [sHole j]))
                            ),
                            ( neg xs_i,
                              sHole i .+. sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) (Apply (Hole xs) [sHole j]))
                            )
                          ]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/map2.fut"
        ( pure $ \(i, n, h1, h2) ->
            let inds_i = sym2SoP $ Apply (Hole h2) [sHole i]
                p = int2SoP 0 :< inds_i :&& inds_i :<= sHole n
             in [ IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body =
                        cases
                          [ (p, sym2SoP $ Apply (Hole h1) [inds_i .-. int2SoP 1]),
                            (neg p, int2SoP 0)
                          ]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/part2indices_numeric_conds.fut"
        ( pure $ \(i, n, xs, j) ->
            let xs_i = sym2SoP $ Apply (Hole xs) [sHole i]
                xs_j = sym2SoP $ Apply (Hole xs) [sHole j]
             in [ IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body =
                        cases
                          [ ( xs_i :== int2SoP 1,
                              sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) (xs_j :== int2SoP 1))
                            ),
                            ( xs_i :/= int2SoP 1,
                              sHole i .+. sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) (xs_j :== int2SoP 1))
                            )
                          ]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/part2indices_predicatefn.fut"
        ( newNameFromString "p" >>= \p -> pure $ \(i, n, xs, j) ->
            let xs_i = Apply (Hole p) [sym2SoP $ Apply (Hole xs) [sHole i]]
                xs_j = Apply (Hole p) [sym2SoP $ Apply (Hole xs) [sHole j]]
             in [ IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body =
                        cases
                          [ ( xs_i,
                              sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) xs_j)
                            ),
                            ( neg xs_i,
                              sHole i .+. sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) xs_j)
                            )
                          ]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/part2indices_predicatefn2.fut"
        ( newNameFromString "p" >>= \p -> pure $ \(i, n, xs, j) ->
            let xs_i = Apply (Hole p) [sym2SoP $ Apply (Hole xs) [sHole i]]
                xs_j = Apply (Hole p) [sym2SoP $ Apply (Hole xs) [sHole j]]
             in [ IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body =
                        cases
                          [ ( xs_i,
                              sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) xs_j)
                            ),
                            ( neg xs_i,
                              sHole i .+. sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) xs_j)
                            )
                          ]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/part3indices.fut"
        ( pure $ \(i, n, cs, j) ->
            let cs_i = sym2SoP $ Apply (Hole cs) [sHole i]
                cs_j = sym2SoP $ Apply (Hole cs) [sHole j]
             in [ IndexFn
                    { shape = [],
                      body =
                        cases
                          [ ( Bool True,
                              sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) (cs_j :== int2SoP 1))
                            )
                          ]
                    },
                  IndexFn
                    { shape = [],
                      body =
                        cases
                          [ ( Bool True,
                              sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) (cs_j :== int2SoP 1))
                                .+. sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) (cs_j :== int2SoP 2))
                            )
                          ]
                    },
                  IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body =
                        cases
                          [ ( cs_i :== int2SoP 2,
                              -- Mind the gap in the sums due to the above predicate simplifying a -1 away.
                              sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) (cs_j :== int2SoP 1))
                                .+. sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) (cs_j :== int2SoP 1))
                                .+. sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) (cs_j :== int2SoP 2))
                            ),
                            ( cs_i :== int2SoP 1,
                              sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) (cs_j :== int2SoP 1))
                            ),
                            ( (cs_i :/= int2SoP 1) :&& (cs_i :/= int2SoP 2),
                              sHole i
                                .+. sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) (cs_j :== int2SoP 1))
                                .+. sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) (cs_j :== int2SoP 2))
                            )
                          ]
                    }
                ]
        ),
      -- mkTest
      --   "tests/indexfn/mk_flag_array.fut"
      --   ( newNameFromString "k" >>= \k ->
      --       newNameFromString "j" >>= \j ->
      --         newNameFromString "zero" >>= \zero -> pure $ \(i, m, xs, shape) ->
      --           let sum_km1 = sym2SoP $ Sum j (int2SoP 0) (sVar k .-. int2SoP 1) (Apply (Hole shape) [sVar j])
      --               sum_mm1 = sym2SoP $ Sum j (int2SoP 0) (sHole m .-. int2SoP 1) (Apply (Hole shape) [sVar j])
      --            in [ IndexFn
      --                   { shape = [],
      --                     body = cases [(Bool True, sum_mm1)]
      --                   },
      --                 IndexFn
      --                   { shape = [[Forall i (Cat k (sHole m) sum_km1)]],
      --                     body =
      --                       cases
      --                         [ (sVar i :== sum_km1, sym2SoP $ Apply (Hole xs) [sVar k]),
      --                           (sVar i :/= sum_km1, sHole zero)
      --                         ]
      --                   }
      --               ]
      --   ),
      mkTest
        "tests/indexfn/mk_flag_array.fut"
        ( do
            -- sum binder for the aoa_len expression
            j <- newNameFromString "j"

            -- iterators for the flattened flags representation
            k <- newNameFromString "k"
            off <- newNameFromString "i"

            -- Holes for the 2 iota bounds
            d0 <- newNameFromString "d"
            d1 <- newNameFromString "d"

            -- hole for the opaque function used after normalisation
            hf <- newNameFromString "f"

            pure $ \(_i, m, shape, _z) ->
              [ -- 1) aoa_len: sum_{j=0..m-1} shape[j]
                IndexFn
                  { shape = [],
                    body =
                      cases
                        [ ( Bool True,
                            sym2SoP $
                              Sum
                                j
                                (int2SoP 0)
                                (sHole m .-. int2SoP 1)
                                (Apply (Hole shape) [sVar j])
                          )
                        ]
                  },

                -- 2) flags: now represented as a flattened 2-iterator dimension.
                -- We don't match the internal guard structure here; we match the
                -- normalised "True => f(k,off)" form that shows up after rewriting.
                IndexFn
                  { shape = [[Forall k (Iota (sHole d0)), Forall off (Iota (sHole d1))]],
                    body =
                      cases
                        [ ( Bool True,
                            sym2SoP $ Apply (Hole hf) [sVar k, sVar off]
                          )
                        ]
                  }
              ]
        ),
      mkTest
        "tests/indexfn/segment_sum.fut"
        ( pure $ \(i, n, xs, flags) ->
            let xs_i = sym2SoP $ Apply (Hole xs) [sHole i]
                flags_i = Apply (Hole flags) [sHole i]
             in [ IndexFn
                    { shape = [[Forall i (Iota (sHole n))]],
                      body =
                        cases
                          [ ((sVar i :== int2SoP 0) :|| flags_i, xs_i),
                            ((sVar i :/= int2SoP 0) :&& Not flags_i, xs_i .+. sym2SoP Recurrence)
                          ]
                    }
                ]
        ),
      mkTest
        "tests/indexfn/segment_ids.fut"
        ( pure $ \(i, m, k, b) ->
            [ IndexFn
                { shape = [[Forall i (Cat k (sHole m) (sHole b))]],
                  body = cases [(Bool True, sHole k)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/part2indicesL.fut"
        ( newNameFromString "csL" >>= \csL ->
            newNameFromString "shape" >>= \shape ->
              newNameFromString "j" >>= \j -> pure $ \(i, m, k, b) ->
                let int = int2SoP
                    csL_i = Apply (Hole csL) [sHole i]
                    seg_k_start = sym2SoP $ Sum j (int 0) (sHole k .-. int 1) (Apply (Hole shape) [sHole j])
                    seg_k_end = int (-1) .+. sym2SoP (Sum j (int 0) (sHole k) (Apply (Hole shape) [sHole j]))
                 in [ IndexFn
                        { shape = [[Forall i (Cat k (sHole m) (sHole b))]],
                          body =
                            cases
                              [ ( csL_i,
                                  -- offset at segment k
                                  seg_k_start
                                    -- number of trues in this segment up to and including current index
                                    .+. sym2SoP (Sum j seg_k_start (sHole i .-. int 1) (Apply (Hole csL) [sHole j]))
                                ),
                                ( neg csL_i,
                                  -- global index
                                  sHole i
                                    -- plus number of trues that come after this index in the current segment
                                    .+. sym2SoP (Sum j (sHole i .+. int 1) seg_k_end (Apply (Hole csL) [sHole j]))
                                )
                              ]
                        }
                    ]
        ),
      mkTest
        "tests/indexfn/filter_indices.fut"
        ( newNameFromString "xs" >>= \xs ->
            newNameFromString "n" >>= \n ->
              newNameFromString "p" >>= \p -> pure $ \(i, _, _, j) ->
                let p_xs arg = Apply (Hole p) [sym2SoP $ Apply (Hole xs) [sHole arg]]
                 in [ IndexFn
                        { shape = [],
                          body =
                            cases
                              [ ( Bool True,
                                  sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) (p_xs j))
                                )
                              ]
                        },
                      IndexFn
                        { shape = [[Forall i (Iota (sHole n))]],
                          body =
                            cases
                              [ ( p_xs i,
                                  sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) (p_xs j))
                                ),
                                ( neg (p_xs i),
                                  int2SoP (-1)
                                )
                              ]
                        }
                    ]
        ),
      mkTest
        "tests/indexfn/partition.fut"
        ( newNameFromString "j" >>= \j ->
            newNameFromString "p" >>= \p -> pure $ \(i, n, xs, _) ->
              [ IndexFn
                  { shape = [],
                    body =
                      cases
                        [ ( Bool True,
                            sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) (Apply (Hole p) [sym2SoP $ Apply (Hole xs) [sHole j]]))
                          )
                        ]
                  },
                IndexFn
                  { shape = [[Forall i (Iota (sHole n))]],
                    body =
                      cases [(Bool True, sym2SoP $ Apply (Hole xs) [sHole i])]
                  }
              ]
        ),
      mkTest
        "tests/indexfn/partition2_alt.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases
                      [(Bool True, sym2SoP $ Apply (Hole xs) [sHole i])]
                }
            ]
        ),
      mkTest
        "tests/indexfn/seg_partition.fut"
        ( pure $ \(i, n, xs, _) ->
            -- Match any output index function; we test whether the intermediate analysis is OK (bounds checking, property verification).
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases [(Bool True, sym2SoP $ Apply (Hole xs) [sHole i])]
                }
            ]
        ),
      mkTest
        "tests/indexfn/partition3.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases [(Bool True, sym2SoP $ Apply (Hole xs) [sHole i])]
                }
            ]
        ),
      mkTest
        "tests/indexfn/filter.fut"
        ( newNameFromString "x" >>= \x ->
            newNameFromString "j" >>= \j -> pure $ \(i, n, xs, p) ->
              let xs_j = Apply (Hole p) [sym2SoP $ Apply (Hole xs) [sHole j]]
                  m = sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) xs_j)
               in [ IndexFn
                      { shape = [[Forall i (Iota m)]],
                        body =
                          cases [(Bool True, sym2SoP $ Apply (Hole x) [sHole i])]
                      }
                  ]
        ),
      mkTest
        "tests/indexfn/filter_irreg.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases [(Bool True, sym2SoP $ Apply (Hole xs) [sHole i])]
                }
            ]
        ),
      mkTest
        "tests/indexfn/maxMatch.fut"
        ( pure $ \(i, n, is_inv, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases
                      [(Bool True, sym2SoP $ Apply (Hole is_inv) [sHole i])]
                }
            ]
        ),
      mkTest
        "tests/indexfn/maxMatch_2d.fut"
        ( pure $ \(i, n, is_inv, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  body =
                    cases
                      [(Bool True, sym2SoP $ Apply (Hole is_inv) [sHole i])]
                }
            ]
        ),
      mkTest
        "tests/indexfn/kmeans_kernel.fut"
        ( pure $ \(anything, _, _, _) ->
            -- Match anything here; this test merely checks bounds in the program.
            [ IndexFn
                { shape = [],
                  body =
                    cases
                      [(Bool True, sHole anything)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/nd_map-map.fut"
        ( newNameFromString "j" >>= \j -> pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota $ sHole n)], [Forall j (Iota $ int2SoP 2)]],
                  body =
                    cases
                      [(Bool True, sym2SoP (Apply (Hole xs) [sHole i]) .+. sHole j)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/nd_map-scan.fut"
        ( newNameFromString "j" >>= \j -> pure $ \(i, n, _, k) ->
            [ IndexFn
                { shape = [[Forall i (Iota $ sHole n)], [Forall j (Iota $ int2SoP 2)]],
                  body =
                    cases
                      [(Bool True, sym2SoP (Sum k (int2SoP 1) (sHole j) (Hole k)))]
                }
            ]
        ),
      mkTest
        "tests/indexfn/nd_expansion.fut"
        ( newNameFromString "j" >>= \j -> pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota $ sHole n)], [Forall j (Iota $ int2SoP 2)]],
                  body =
                    cases
                      [(Bool True, int2SoP 2 .*. sym2SoP (Apply (Hole xs) [sVar i]) .+. sHole j)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/if-array-type.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota $ sHole n)]],
                  body =
                    cases
                      [(Bool True, sym2SoP (Apply (Hole xs) [sVar i]))]
                },
              IndexFn
                { shape = [[Forall i (Iota $ sHole n)]],
                  body =
                    cases
                      [(Bool True, sym2SoP (Apply (Hole xs) [sVar i]))]
                }
            ]
        ),
      mkTest
        "tests/indexfn/zipArgs2d.fut"
        ( newNameFromString "j" >>= \j -> pure $ \(i, n, m, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota $ sHole n)], [Forall j (Iota $ sHole m)]],
                  body =
                    cases
                      [(Bool True, sHole i .+. sHole j .+. int2SoP 1)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/primes.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  -- matches anything; we're just checking the program.
                  body = cases [(Bool True, sHole xs)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/mis.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  -- matches anything; we're just checking the program.
                  body = cases [(Bool True, sHole xs)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/quickhull.fut"
        ( pure $ \(i, n, xs, _) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))]],
                  -- matches anything; we're just checking the program.
                  body = cases [(Bool True, sHole xs)]
                }
            ]
        ),
      mkTest
        "tests/indexfn/srad.fut"
        ( newNameFromString "j" >>= \j -> pure $ \(i, n, m, xs) ->
            [ IndexFn
                { shape = [[Forall i (Iota (sHole n))], [Forall j (Iota (sHole m))]],
                  -- matches anything; we're just checking the program.
                  body = cases [(Bool True, sym2SoP $ Apply (Hole xs) [sHole i, sHole j])]
                }
            ]
       )
      -- mkTest
      --   "tests/indexfn/quickhull.fut"
      --   ( pure $ \(i, n, xs, _) ->
      --       [ IndexFn
      --           { shape = [Forall i (Iota (sHole n))],
      --             -- matches anything; we're just checking the program.
      --             body = cases [(Bool True, sHole xs)]
      --           }
      --       ]
      --   ),
      -- mkTest
      --   "tests/indexfn/lolhull.fut"
      --   ( pure $ \(i, n, xs, _) ->
      --       [ IndexFn
      --           { shape = [Forall i (Iota (sHole n))],
      --             -- matches anything; we're just checking the program.
      --             body = cases [(Bool True, sHole xs)]
      --           }
      --       ]
      --   )
      -- mkTest
      --   "tests/indexfn/part3indices_alternative.fut"
      --   ( newNameFromString "q" >>= \q -> pure $ \(i, n, p, j) ->
      --       let p_i = Apply (Hole p) [sHole i]
      --           p_j = Apply (Hole p) [sHole j]
      --           q_i = Apply (Hole q) [sHole i]
      --           q_j = Apply (Hole q) [sHole j]
      --        in [ IndexFn
      --               { shape = [],
      --                 body =
      --                   cases
      --                     [ ( Bool True,
      --                         sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) p_j)
      --                       )
      --                     ]
      --               },
      --             IndexFn
      --               { shape = [],
      --                 body =
      --                   cases
      --                     [ ( Bool True,
      --                         sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) p_j)
      --                           .+. sym2SoP (Sum j (int2SoP 0) (sHole n .-. int2SoP 1) q_j)
      --                       )
      --                     ]
      --               },
      --             IndexFn
      --               { shape = [Forall i (Iota (sHole n))],
      --                 body =
      --                   cases
      --                     [ ( p_i,
      --                         sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) p_j)
      --                       ),
      --                       ( neg p_i :&& q_i,
      --                         -- Mind the gap in the sums due to the above predicate simplifying a -1 away.
      --                         sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) p_j)
      --                           .+. sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) p_j)
      --                           .+. sym2SoP (Sum j (int2SoP 0) (sHole i .-. int2SoP 1) q_j)
      --                       ),
      --                       ( neg p_i :&& neg q_i,
      --                         sHole i
      --                           .+. sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) p_j)
      --                           .+. sym2SoP (Sum j (sHole i .+. int2SoP 1) (sHole n .-. int2SoP 1) q_j)
      --                       )
      --                     ]
      --               }
      --           ]
      --   )
      -- mkTest
      --   "tests/indexfn/for_postcondition.fut"
      --   ( pure $ \(i, n, xs, _) ->
      --       [ IndexFn
      --           { shape = [[Forall i (Iota (sHole n))]],
      --             body =
      --               cases
      --                 [ (sym2SoP (Apply (Hole xs) [sHole i]) :>= int2SoP 0, sym2SoP (Apply (Hole xs) [sHole i])),
      --                   (sym2SoP (Apply (Hole xs) [sHole i]) :< int2SoP 0, int2SoP 0)
      --                 ]
      --           }
      --       ]
      --   ),
      -- mkTest
      --   "tests/indexfn/for_precondition.fut"
      --   ( pure $ \(i, n, xs, _) ->
      --       [ IndexFn
      --           { shape = [[Forall i (Iota (sHole n))]],
      --             body = cases [(Bool True, sym2SoP (Apply (Hole xs) [sHole i]))]
      --           }
      --       ]
      --   ),
      -- mkTest
      --   "tests/indexfn/for_parsing.fut"
      --   ( pure $ \(i, _, xs, _) ->
      --       [ IndexFn
      --           { shape = [],
      --             body =
      --               cases
      --                 [ (Bool True, sym2SoP . Prop $ For xs (Predicate i Boolean))
      --                 ]
      --           }
      --       ]
      --   )
    ]
  where
    mkTest programFile expectedPat = testCase (basename programFile) $ do
      (_, imports, vns) <- readProgramOrDie programFile
      let last_import = case reverse imports of
            [] -> error "No imports"
            x : _ -> x
      let vbs = getValBinds last_import
      let (actuals, expecteds) = unzip $ runTest vns vbs expectedPat
      when (null actuals) $
        assertFailure "The last value binding does not create an index function."
      actuals @??= expecteds

    basename = drop (length prefix)
      where
        prefix :: String = "tests/indexfn/"

    getValBinds = mapMaybe getValBind . E.progDecs . fileProg . snd

    getValBind (E.ValDec vb) = Just vb
    getValBind _ = Nothing

    -- We need to make the index function and run unification using
    -- the same VNameSource, otherwise the variables in the index function
    -- are likely to be considered bound quantifier variables.
    runTest vns vbs expectedPat = fst . flip runIndexFnM vns $ do
      i <- newNameFromString "i"
      x <- newNameFromString "h"
      y <- newNameFromString "h"
      z <- newNameFromString "h"
      let preceding_vbs = init vbs
      let last_vb = last vbs
      -- Evaluate expectedPat first for any side effects like debug toggling.
      pat <- expectedPat
      let expecteds = pat (i, x, y, z)
      forM_ preceding_vbs mkIndexFnValBind
      actuals <- mkIndexFnValBind last_vb
      forM (zip expecteds actuals) $ \(expected, actual) -> do
        s <- unify expected actual
        case s of
          Nothing ->
            renameSame actual expected
          Just s' -> do
            e <- subIndexFn s' expected
            renameSame actual e

    sHole = sym2SoP . Hole

    sVar = sym2SoP . Var