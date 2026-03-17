module Futhark.Analysis.Properties.SoPUtil
  ( sumSoP
  )
where

import Data.Map qualified as M
import Language.Futhark (VName)
import Futhark.SoP.SoP (SoP(..), int2SoP, isConstTerm, sym2SoP, (.*.), (.+.), (.-.))
import Futhark.Analysis.Properties.Symbol (Symbol(..), sop2Symbol)

sumSoP :: VName -> SoP Symbol -> SoP Symbol -> SoP Symbol -> SoP Symbol
sumSoP i lb ub (SoP ts)
  | M.null ts = int2SoP 0
  | otherwise =
      foldl
        (.+.)
        (int2SoP 0)
        [ sumTerm term coeff | (term, coeff) <- M.toList ts
        ]
  where
    -- Sum over a single SoP term.
    -- If the term is constant 1, then sum_{i=lb}^{ub-1} 1 = ub-lb.
    sumTerm term coeff
      | isConstTerm term =
          int2SoP coeff .*. (ub .-. lb .+. int2SoP 1)
      | otherwise =
          let oneTerm = SoP (M.singleton term 1)
           in int2SoP coeff .*. sym2SoP (Sum i lb ub (sop2Symbol oneTerm))