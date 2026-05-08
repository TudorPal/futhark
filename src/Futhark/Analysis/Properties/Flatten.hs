{-# LANGUAGE LambdaCase #-}

module Futhark.Analysis.Properties.Flatten (lookupII, from1Dto2D, from1Dto2DM, unflatten, mkERow) where

import Data.List (tails)
import Data.Map qualified as M
import Data.Set qualified as S
import Futhark.Analysis.Properties.IndexFn
import Futhark.Analysis.Properties.IndexFnPlus ()
import Futhark.Analysis.Properties.Monad
import Futhark.Analysis.Properties.Symbol
import Futhark.Analysis.Properties.Unify
import Futhark.Analysis.Properties.SoPUtil (sumSoP)
import Futhark.MonadFreshNames (newVName)
import Futhark.SoP.SoP (SoP (SoP), int2SoP, isConstTerm, sym2SoP, (.*.), (.+.), (.-.))
import Futhark.Util.Pretty (Pretty)
import Language.Futhark (VName)

mkERow :: VName -> SoP Symbol -> IndexFnM (SoP Symbol)
mkERow i2 e3 = do
  j <- newVName "j"
  let ub   = sym2SoP (Var i2) .-. int2SoP 1
  let e3_j = rep (mkRep i2 (sym2SoP (Var j))) e3
  pure $ sumSoP j (int2SoP 0) ub e3_j

from1Dto2D :: Quantified Domain -> Quantified Domain -> SoP Symbol -> [(VName, SoP Symbol)]
from1Dto2D (Forall i (Iota n)) (Forall j (Iota m)) e_idx
  | i `S.notMember` fv m =
      let idx = sym2SoP (Ix n m e_idx)
       in [(i, idx), (j, e_idx .-. idx .*. m)]
  | otherwise =
    error $
      "from1Dto2D: cannot apply SubFlat-Simplified because inner bound depends on outer iterator.\n"
        <> "  outer iterator: " <> show i <> "\n"
        <> "  inner bound m: " <> show m <> "\n"
        <> "  flat index e_idx: " <> show e_idx <> "\n"
from1Dto2D _ _ _ = undefined

from1Dto2DM :: Quantified Domain -> Quantified Domain -> SoP Symbol -> IndexFnM [(VName, SoP Symbol)]
from1Dto2DM (Forall i1 (Iota e2)) (Forall i2 (Iota e3)) e_idx
  | i1 `S.notMember` fv e3 =
      let outer = sym2SoP (Ix e2 e3 e_idx)
       in pure [(i1, outer), (i2, e_idx .-. outer .*. e3)]

  | otherwise = do
      -- printM 3 "from1Dto2D irregular start"
      -- printM 3 $ "  eidx: " <> prettyStr e_idx

      j <- newVName "j"

      -- row start as a function of i1
      let ub    = sym2SoP (Var i1) .-. int2SoP 1
      let e3_j  = rep (mkRep i1 (sym2SoP (Var j))) e3
      -- printM 3 "  before eRow"
      let eRow  = sumSoP j (int2SoP 0) ub e3_j
      -- printM 3 "  after eRow"

      -- %D(e_idx)
      let outer = sym2SoP (Ix e2 e3 e_idx)

      -- eRow[%D(e_idx) / i1]
      let eRowOuter = rep (mkRep i1 outer) eRow

      pure
        [ (i1, outer)
        , (i2, e_idx .-. eRowOuter)
        ]
from1Dto2DM _ _ _ = undefined

flatIndices :: [[Quantified Domain]] -> [SoP Symbol]
flatIndices = map flattenIndex

flattenIndex :: [Quantified Domain] -> SoP Symbol
flattenIndex dim
  | S.fromList (map boundVar dim) `S.disjoint` mconcat (map fv dim),
    all (\case (Forall _ (Iota {})) -> True; _ -> False) dim =
      let nss = drop 1 (tails [n | Forall _ (Iota n) <- dim])
       in foldl
            (.+.)
            (int2SoP 0)
            [multiply i ns | (i, ns) <- zip (map boundVar dim) nss]
  where
    multiply i [] = sym2SoP (Var i)
    multiply i ns = sym2SoP (Var i) .*. foldl1 (.*.) ns
flattenIndex _ = undefined

unflatten :: IndexFn -> IndexFn
unflatten f = f {shape = map (: []) (concat (shape f))}

lookupII :: Domain -> IndexFn -> IndexFnM (VName, IndexFn)
lookupII dom def = do
  v <- unisearch dom =<< getII
  case v of
    Just res -> pure res
    Nothing -> do
      vn <- newVName "II"
      insertII dom (vn, def)
      pure (vn, def)

-- Search a mapping using unification for equality checks.
unisearch :: (Ord v, Unify v Symbol, Pretty v) => v -> M.Map v a -> IndexFnM (Maybe a)
unisearch x mapping = do
  case mapping M.!? x of
    Just v ->
      -- Exact match.
      pure (Just v)
    Nothing -> do
      -- Search for matches using unification.
      matches :: [(a, Maybe (Substitution Symbol))] <-
        mapM (\(k, v) -> (v,) <$> unify k x) (M.toList mapping)
      case matches of
        [] -> pure Nothing
        [(v, _)] ->
          pure (Just v)
        _ -> error "unisearch: multiple matches"
