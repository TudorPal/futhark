{-# OPTIONS_GHC -Wno-orphans #-}

module Futhark.Analysis.Properties.IndexFnPlus
  ( domainStart,
    domainEnd,
    repIndexFn,
    subIndexFn,
    repCases,
    intervalEnd,
    repDomain,
    unifyIndexFnWith,
    intervalStart,
    index,
    dimSize,
    dimEnd,
  )
where

import Control.Monad (foldM)
import Control.Monad.Trans.Maybe (MaybeT)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Maybe (mapMaybe)
import Data.Set qualified as S
import Futhark.Analysis.Properties.IndexFn
import Futhark.Analysis.Properties.Monad
import Futhark.Analysis.Properties.Symbol
import Futhark.Analysis.Properties.SymbolPlus (repVName)
import Futhark.Analysis.Properties.Unify (FreeVariables (..), Renameable (..), Rep (..), Replacement, ReplacementBuilder (..), Substitution (..), Unify (..), freshNameFromString, unifies_)
import Futhark.Analysis.Properties.Util (prettyName)
import Futhark.SoP.SoP (SoP (SoP), int2SoP, isConstTerm, sym2SoP, (.*.), (.+.), (.-.))
import Futhark.Util.Pretty (Pretty (pretty), align, comma, commastack, hang, indent, line, parens, punctuate, sep, softline, stack, (<+>), (</>))
import Futhark.MonadFreshNames (newVName)
import Futhark.Analysis.Properties.SoPUtil (sumSoP)
import Language.Futhark (VName)

domainStart :: Domain -> SoP Symbol
domainStart (Iota _) = int2SoP 0
domainStart (Cat {}) = error "Cat domain should be gone (domainStart)"
-- domainStart (Cat k _ b) = rep (mkRep k (int2SoP 0 :: SoP Symbol)) b

domainEnd :: Domain -> SoP Symbol
domainEnd (Iota n) = n .-. int2SoP 1
domainEnd   (Cat {}) = error "Cat domain should be gone (domainEnd)"
-- domainEnd (Cat k m b) = rep (mkRep k m) b .-. int2SoP 1

intervalStart :: Domain -> SoP Symbol
-- intervalStart (Cat {}) = error "Cat domain should be gone (intervalStart)"
intervalStart (Cat _ _ b) = b
intervalStart (Iota _) = error "intervalStart on iota"

intervalEnd :: Domain -> SoP Symbol
-- intervalEnd   (Cat {}) = error "Cat domain should be gone (intervalEnd)"
intervalEnd (Cat k _ b) = rep (mkRep k (sym2SoP (Var k) .+. int2SoP 1)) b .-. int2SoP 1
intervalEnd (Iota _) = error "intervalEnd on iota"

dimStart :: [Quantified Domain] -> SoP Symbol
dimStart [] = undefined
dimStart (dim : _) = domainStart (formula dim)

dimEnd :: [Quantified Domain] -> SoP Symbol
dimEnd [] = undefined
dimEnd [d] = domainEnd (formula d)
dimEnd [Forall i (Iota n), Forall _ (Iota m)]
  -- Flat regular dimension.
  | i `S.notMember` fv m =
      n .*. m .-. int2SoP 1
-- Segmented flattened dimension.
-- Total size is sum_{k=0}^{m-1} len(k), so the last valid index is that - 1.
dimEnd [Forall k (Iota m), Forall _ (Iota len)]
  | k `S.member` fv len =
    -- sym2SoP (Sum k 0 m (sop2Symbol len)) - 1   -- but len is a compound expression, so we need to sum over it properly.
      let ub = m .-. int2SoP 1
       in sumSoP k (int2SoP 0) ub len .-. int2SoP 1
dimEnd _ = error "dont know why it should get here"

dimSize :: [Quantified Domain] -> SoP Symbol
dimSize d = dimEnd d .-. dimStart d .+. int2SoP 1

segStart :: VName -> VName -> SoP Symbol -> SoP Symbol
segStart t k len =
  let ub = sym2SoP (Var k) .-. int2SoP 1
      len_t = rep (mkRep k (sym2SoP (Var t))) len
  in sumSoP t (int2SoP 0) ub len_t

index :: [Quantified Domain] -> SoP Symbol
index [Forall i _] = sym2SoP (Var i)
index [Forall i _, Forall j (Iota m)]
  -- Flat regular dimension.
  | i `S.notMember` fv m =
      sym2SoP (Var i) .*. m .+. sym2SoP (Var j)
index [Forall k (Iota _m), Forall j (Iota len)]
  -- segmented flattened dimension
  -- flat(k,j) = sum_{t=0}^{k-1} len(t) + j
  -- sum_{k=0}^{k-1} len(k)
  | k `S.member` fv len =
      let t = k
      in segStart t k len .+. sym2SoP (Var j)
index _ =
  error "dont know why it should get here"

-- in the original `index` function we wrote `let t = k`, but that is wrong 
-- because `t` is supposed to be the loop variable inside the sum, while `k` 
-- is the segment index from the outside. the `Sum` expression binds its loop variable, 
-- so if we reuse the name `k` then the sum ends up binding `k` and it shadows 
-- the outer `k`. with a monadic `indexM` function we can create a fresh name for the sum binder, 
-- like `t <- newVName "t"`. then we can safely build the expression `sum_{t=0}^{k-1} len(t) + j`
-- without any name clashes, because `t` is guaranteed to be different from `k`.

indexM :: [Quantified Domain] -> IndexFnM (SoP Symbol)
indexM [Forall i _] =
  pure $ sym2SoP (Var i)
indexM [Forall i _, Forall j (Iota m)]
  -- flat regular dimension
  | i `S.notMember` fv m =
      pure $ sym2SoP (Var i) .*. m .+. sym2SoP (Var j)
indexM [Forall k (Iota _m), Forall j (Iota len)]
  -- segmented flattened dimension
  -- flat(k,j) = sum_{t=0}^{k-1} len(t) + j
  | k `S.member` fv len = do
      t <- newVName "t"
      let ub = sym2SoP (Var k) .-. int2SoP 1
      let len_t = rep (mkRep k (sym2SoP (Var t))) len
      let start = sumSoP t (int2SoP 0) ub len_t
      pure $ start .+. sym2SoP (Var j)
indexM ds =
  error $ "indexM: not implemented for dimension " <> show ds

-------------------------------------------------------------------------------
-- Pretty.
-------------------------------------------------------------------------------
instance (Pretty a, Pretty b) => Pretty (Cases a (SoP b)) where
  pretty (Cases cs) =
    stack (map prettyCase (NE.toList cs))
    where
      prettyCase (p, e) = "|" <+> pretty p <+> "⇒ " <> softline <> indent 2 (hang 2 $ prettySoP e)

      -- Like pretty instance for SoP, but inserts soft linebreaks between top-level +.
      prettySoP (SoP ts)
        | M.null ts = "0"
        | otherwise =
            mconcat $
              punctuate (softline <> "+ ") $
                map (uncurry pTerm) $
                  M.toList ts

      pTerm term n
        | isConstTerm term = pretty n
        | n == 1 = pretty term
        | otherwise = pretty n <> "*" <> pretty term

instance Pretty Domain where
  pretty (Iota n) = parens $ "0 .." <+> parens (pretty n)
  pretty dom@(Cat k m b) =
    "⊎"
      <> prettyName k
      <> "="
      <> parens ("0 .." <+> pretty (m .-. int2SoP 1))
        <+> "["
      <> align (sep $ punctuate comma [pretty b, "...", pretty (intervalEnd dom)])
      <> "]"

instance Pretty Iterator where
  pretty (Forall i (Iota n)) =
    "for " <> prettyName i <+> "<" <+> pretty n <+> "."
  pretty (Forall i dom@(Cat k m seg)) =
    "for "
      <> prettyName i
        <+> "∈"
        <+> "⊎"
      <> parens (prettyName k <+> "<" <+> pretty m)
        <+> "["
      <> commastack [pretty seg, "...", pretty (intervalEnd dom)]
      <> "]"
        <+> "."
      <> line

instance Pretty IndexFn where
  pretty (IndexFn [] e) = "•" <+> pretty e
  pretty (IndexFn iter e) = stack (map pretty iter) </> indent 2 (pretty e)

instance FreeVariables Domain where
  fv (Iota n) = fv n
  fv (Cat k m b) = fv m <> fv b S.\\ S.singleton k

instance FreeVariables Iterator where
  fv (Forall i d) = fv d S.\\ S.singleton i

instance FreeVariables [[Iterator]] where
  fv shape = mconcat (map fv $ concat shape)

instance FreeVariables (Cases Symbol (SoP Symbol)) where
  fv cs = mconcat $ map (\(c, v) -> fv c <> fv v) $ casesToList cs

instance FreeVariables IndexFn where
  fv (IndexFn dims cs) =
    fv_dims <> (fv cs S.\\ bound_all)
    where
      -- flatten the iterator lists so we can fold left to right
      iters = concat dims

      -- all iterator binders are considered bound in the body
      bound_all :: S.Set VName
      bound_all = S.fromList (map boundVar iters)

      -- free vars coming from the iterator domains
      fv_dims :: S.Set VName
      fv_dims = snd $ foldl step (S.empty, S.empty) iters

      -- accumulator is bound vars seen so far and free vars collected so far
      step :: (S.Set VName, S.Set VName) -> Quantified Domain -> (S.Set VName, S.Set VName)
      step (bound_so_far, fv_acc) (Forall i d) =
        let bound' = S.insert i bound_so_far
            -- vars used in the domain minus what is already bound
            fv_d   = fv d S.\\ bound'
        in (bound', fv_acc <> fv_d)

-------------------------------------------------------------------------------
-- Unification.
-------------------------------------------------------------------------------
repCases :: Replacement Symbol -> Cases Symbol (SoP Symbol) -> Cases Symbol (SoP Symbol)
repCases s (Cases cs) = Cases $ NE.map repCase cs
  where
    repCase (a, b) = (sop2Symbol (rep s a), rep s b)

repDomain :: Replacement Symbol -> Domain -> Domain
repDomain s (Iota n) = Iota (rep s n)
repDomain s (Cat k m b) = Cat k (rep s m) (rep s b)

repIterator :: Replacement Symbol -> Quantified Domain -> Quantified Domain
repIterator s (Forall i dom) = Forall (repVName s i) (repDomain s dom)

repIndexFn :: Replacement Symbol -> IndexFn -> IndexFn
repIndexFn s (IndexFn dims body) = IndexFn (map (map (repIterator s)) dims) (repCases s body)

subIndexFn :: Substitution Symbol -> IndexFn -> IndexFnM IndexFn
subIndexFn s indexfn = repIndexFn (mapping s) <$> rename (vns s) indexfn

instance (Renameable a, Renameable b) => Renameable (Cases a b) where
  rename_ vns tau (Cases cs) = Cases <$> mapM re cs
    where
      re (p, q) = (,) <$> rename_ vns tau p <*> rename_ vns tau q

instance Renameable Domain where
  rename_ vns tau (Cat xn m b) = do
    (xm, vns') <- freshNameFromString vns "k"
    let tau' = M.insert xn xm tau
    Cat xm <$> rename_ vns' tau' m <*> rename_ vns' tau' b
  rename_ vns tau (Iota n) = Iota <$> rename_ vns tau n

instance Renameable Iterator where
  -- NOTE that i is not renamed.
  rename_ vns tau (Forall i dom) = Forall i <$> rename_ vns tau dom

instance Renameable IndexFn where
  rename_ vns tau (IndexFn dimss body) = do
    let (ns, dims) = flatten dimss
    (vns', tau', xs) <- foldM (\(v, t, ds) d -> append3rd ds <$> renameIter v t d) (vns, tau, []) dims
    let dims' = reverse xs
    IndexFn (unflatten ns dims') <$> rename_ vns' tau' body
    where
      append3rd cs (a, b, c) = (a, b, c : cs)
      -- Wraps rename_ on Iterator to also return new state for renaming k in body.
      renameIter v t (Forall i (Cat xn m b)) = do
        (xm, v') <- freshNameFromString v "k"
        let t' = M.insert xn xm t
        dom <- Cat xm <$> rename_ v' t' m <*> rename_ v' t' b
        pure (v', t', Forall i dom)
      renameIter v t it =
        (v,t,) <$> rename_ v t it

      flatten :: [[a]] -> ([Int], [a])
      flatten xss = (map length xss, concat xss)

      unflatten :: [Int] -> [a] -> [[a]]
      unflatten [] _ = []
      unflatten (n : ns) xs =
        let (chunk, rest) = splitAt n xs
         in chunk : unflatten ns rest

instance Unify Domain Symbol where
  unify_ k (Iota n) (Iota m) = unify_ k n m
  unify_ k (Cat _ m1 b1) (Cat _ m2 b2) = do
    s <- unify_ k m1 m2
    (s <>) <$> unify_ k (rep s b1) (rep s b2)
  unify_ _ _ _ = fail "Incompatible domains"

instance Unify (Cases Symbol (SoP Symbol)) Symbol where
  unify_ k (Cases cs1) (Cases cs2) = do
    s <- unifies_ k (map fst xs) (map fst ys)
    s2 <- unifies_ k (map (rep s . snd) xs) (map (rep s . snd) ys)
    pure $ s <> s2
    where
      xs = NE.toList cs1
      ys = NE.toList cs2

instance Unify Iterator Symbol where
  unify_ k (Forall i d1) (Forall j d2) = do
    s <- if i == j then pure mempty else unify_ k (Hole i) (Var j)
    (s <>) <$> unify_ k (repDomain s d1) (repDomain s d2)

instance Unify [[Iterator]] Symbol where
  unify_ k xss yss
    | length xss == length yss,
      map length xss == map length yss =
        go (zip (concat xss) (concat yss))
    | otherwise = fail "different lengths"
    where
      go [] = pure mempty
      go (u : us) = do
        s0 <- uncurry (unify_ k) u
        foldM
          (\s (a, b) -> (s <>) <$> unify_ k (repIterator s a) (repIterator s b))
          s0
          us

instance Unify IndexFn Symbol where
  unify_ = unifyIndexFnWith unify_

unifyIndexFnWith ::
  (VName -> Cases Symbol (SoP Symbol) -> Cases Symbol (SoP Symbol) -> MaybeT IndexFnM (Replacement Symbol)) ->
  VName ->
  IndexFn ->
  IndexFn ->
  MaybeT IndexFnM (Replacement Symbol)
unifyIndexFnWith unifyBody k (IndexFn dims1 body1) (IndexFn dims2 body2) = do
  s <- unify_ k dims1 dims2
  (s <>) <$> unifyBody k (repCases s body1) (repCases s body2)
