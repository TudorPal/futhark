-- Index function substitution.
{-# LANGUAGE LambdaCase #-}

module Futhark.Analysis.Properties.Substitute ((@), subst, propFlattenOnce) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, when, (<=<), zipWithM)
import Control.Monad.RWS (lift)
import Control.Monad.Trans.Maybe (MaybeT (..), hoistMaybe, runMaybeT)
import Data.Functor ((<&>))
import Data.Map qualified as M
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Set qualified as S
import Data.List (nubBy, isInfixOf)
import Data.List.NonEmpty qualified as NE
import Futhark.Analysis.Properties.AlgebraBridge (answerFromBool, orM, simplify, ($==), addRelShape, addRelSymbol)
import Futhark.Analysis.Properties.Flatten (from1Dto2D, lookupII, from1Dto2DM, mkERow)
import Futhark.Analysis.Properties.IndexFn
import Futhark.Analysis.Properties.IndexFnPlus (domainEnd, intervalEnd, intervalStart, repCases, repDomain, repIndexFn)
import Futhark.Analysis.Properties.Monad
import Futhark.Analysis.Properties.Query (Answer (..), Query (CaseCheck), askQ, unifiesWith)
import Futhark.Analysis.Properties.Rewrite (rewrite, rewriteWithoutRules, solveIx)
import Futhark.Analysis.Properties.Symbol
import Futhark.Analysis.Properties.Traversals
import Futhark.Analysis.Properties.Unify (Rep (..), Replacement, ReplacementBuilder (..), Substitution (..), Unify (..), fv, renameM)
import Futhark.Analysis.Properties.Util
import Futhark.Analysis.Properties.SoPUtil (sumSoP)
import Futhark.MonadFreshNames (newVName)
import Futhark.SoP.SoP (SoP(SoP), int2SoP, isConstTerm, justSym, sym2SoP, (.*.), (.+.), (.-.))
import Futhark.Util.Pretty (prettyString)
import Language.Futhark (VName)

-- If f has multiple cases, we would not know which case to substitute
-- into quantified symbols (e.g., Sum j a b f(e(j))).
legalArg :: VName -> IndexFn -> IndexFn -> [SoP Symbol] -> Bool
legalArg k g f args =
  let notQuantifier vn = vn < k || or [Just vn == catVar it | it <- concat $ shape g]
   in (hasSingleCase f || all (all notQuantifier . fv) args)
  where
    hasSingleCase = isJust . justSingleCase

-- Substitute applications of (f_name = f) into g.
-- Unlike `subst` this errors if the substitution fails and
-- will not check that indexing is within bounds.
-- We use @ for convenience when substituting intermediate results in Convert.
-- 'g @ (f_name, f)' substitutes name 'f_name' for indexfn 'f' in indexfn 'g'.
-- TODO remove this or deduplicate overlap with `subst`.
(@) :: IndexFn -> (VName, IndexFn) -> IndexFnM IndexFn
dest_fn @ (f_name, _)
  | f_name `S.notMember` fv dest_fn =
      pure dest_fn
dest_fn @ (f_name, f) = do
  k <- newVName "variables after this are quantifiers"
  g <- renameM dest_fn

  go mempty g (legalArg k g f)
  where
    go _ g _ | f_name `S.notMember` fv g = pure g
    go seen g argCheck = do
      app <- getApply seen g
      printM 1337 . gray $ prettyString g
      printM 1337 $ warningString "\t@ " <> gray (prettyString (fst <$> app))
      printM 1337 . gray $ "\t  where " <> prettyString f_name <> " =\n" <> prettyIndent 16 f
      case app of
        Just apply@(_, args)
          | argCheck args -> do
              h <- substituteOnce f g apply
              h' <- go (S.insert (f_name, args) seen) (fromJust h) argCheck
              printM 1337 . gray $ "\t  ->\n" <> prettyIndent 16 h'
              pure h'
          | otherwise -> do
              go (S.insert (f_name, args) seen) g argCheck
        Nothing
          | S.null seen -> do
              -- When converting expressions a function may be substituted without arguments.
              -- This may fail when substituting into an uninterpreted function.
              fromMaybe g <$> substituteOnce f g (Var f_name, [])
          | otherwise -> do
              pure g

    getApply seen = astFold (ASTFolder {foldOnSymbol = getApply_ seen}) Nothing

    getApply_ seen Nothing e@(Apply (Var vn) args)
      | vn == f_name,
        (vn, args) `S.notMember` seen =
          pure $ Just (e, args)
    getApply_ _ acc _ = pure acc

-- getApply = astFold (ASTFolder {foldOnSymbol = getApply_}) Nothing

-- getApply_ Nothing e@(Apply (Var vn) args)
--   | vn == f_name,
--     argCheck e args =
--       pure $ Just (e, args)
-- getApply_ acc _ = pure acc

-- Substitution as defined in the paper.
-- Unlike @ this will attempt to substitute all indexing/applications
-- in the index function and allows those substitutions to fail (no-op).
subst :: IndexFn -> IndexFnM IndexFn
subst indexfn = do
  k <- newVName "variables after this are quantifiers"
  g <- renameM indexfn
  subber (legalArg k g) g

-- mkERow :: VName -> SoP Symbol -> IndexFnM (SoP Symbol)
-- mkERow i2 e3 = do
--   j <- newVName "j"
--   let ub   = sym2SoP (Var i2) .-. int2SoP 1
--   let e3_j = rep (mkRep i2 (sym2SoP (Var j))) e3
--   pure $ sumSoP j (int2SoP 0) ub e3_j

-- Try to apply PropFlatten on dimension k, propagating a flattened domain
-- from f to g.
--
-- Returns Nothing if it does not match (or we cannot prove the required
-- size relation).
propFlattenOnce :: Int -> IndexFn -> IndexFn -> IndexFnM (Maybe IndexFn)
propFlattenOnce k g f = runMaybeT $ do
  if k >= rank g || k >= rank f
    then fail "No match."
    else case (shape g !! k, shape f !! k) of
      ([Forall i1 (Iota e1)], df@[Forall i2 (Iota e2), Forall i3 (Iota e3)]) -> do
        -- printM 3 $ "propFlattenOnce start k=" <> prettyStr k
        -- printM 3 $ "  e1=" <> prettyStr e1
        -- printM 3 $ "  e2=" <> prettyStr e2
        -- printM 3 $ "  e3=" <> prettyStr e3

        if i2 `S.notMember` fv e3
          then do
            ans <- lift (e1 $== e2 .*. e3)
            case ans of
              Yes -> do
                eRow <- lift . rewrite $ sym2SoP (Var i2) .*. e3
                let s = mkRep i1 (eRow .+. sym2SoP (Var i3))
                let (l, _old : r) = splitAt k (shape g)
                let res = g {shape = l <> (df : r), body = repCases s (body g)}
                if res == g
                  then fail "regular PropFlatten made no progress"
                  else pure res
              Unknown ->
                fail "regular PropFlatten could not prove size equality"

          else do
            -- printM 3 "  irregular branch"
            eRow <- lift $ mkERow i2 e3
            end  <- lift . rewrite $ rep (mkRep i2 e2) eRow
            ans  <- lift (e1 $== end)
            -- printM 3 $ "  irregular ans=" <> prettyStr ans
            case ans of
              Yes -> do
                let s = mkRep i1 (eRow .+. sym2SoP (Var i3))
                let (l, _old : r) = splitAt k (shape g)
                let res = g { shape = l <> (df : r), body = repCases s (body g) }
                -- printM 3 $ "  irregular result shape=" <> prettyStr (shape res)
                -- printM 3 $ "  irregular result body=" <> prettyStr (body res)
                -- printM 3 $ "  irregular result full=" <> prettyStr res
                if res == g
                  then fail "irregular PropFlatten made no progress"
                  else pure res
              Unknown ->
                fail "irregular PropFlatten could not prove size equality"
      _ -> fail "No match."

-- Are you substituting xs[i] for xs = for i < e . true => xs[i]?
-- This happens when xs is a formal argument. (So not relevant for flattened arrays.)
trivialSub :: Symbol -> IndexFn -> [SoP Symbol] -> Bool
trivialSub e f args
  | length (shape f) == length args,
    all ((<= 1) . length) (shape f),
    Just e' <- justSym =<< justSingleCase f =
      sym2SoP e == rep dims2args e'
  | otherwise = False
  where
    dims2args =
      mkRepFromList $ zipWith (\[dim] arg -> (boundVar dim, arg)) (shape f) args

subber :: (IndexFn -> [SoP Symbol] -> Bool) -> IndexFn -> IndexFnM IndexFn
subber argCheck g = do
  go mempty
  where
    go seen = do
      apply <- getApply seen g
      ixfns <- getIndexFns
      when (isJust apply) $ do
        printM 1337 $ warningString "subst " <> prettyString seen
        printM 1337 . gray $ prettyIndent 4 g
        printM 1337 . gray $ "\t@ " <> prettyString apply
      case apply of
        Just (e, vn, args)
          | Just [f] <- ixfns M.!? vn,
            not (trivialSub e f args),
            argCheck f args -> do
              g' <- substituteOnce f g (e, args)
              case g' of
                Just new_fn | new_fn /= g -> do
                  subst =<< rewriteWithoutRules new_fn
                _ ->
                  go (S.insert (vn, args) seen)
        Just (_, vn, args)
          | otherwise ->
              go (S.insert (vn, args) seen)
        Nothing ->
          pure g

    getApply seen = astFold (ASTFolder {foldOnSymbol = getApply_ seen}) Nothing

    getApply_ seen Nothing e@(Apply (Var vn) args)
      | (vn, args) `S.notMember` seen =
          pure $ Just (e, vn, args)
    getApply_ _ acc _ = pure acc

-- TODO not sure this is useful
-- eliminateII :: IndexFn -> IndexFnM IndexFn
-- eliminateII f@(IndexFn [Forall i d@(Cat k _ _)] _) = do
--   res <- unisearch d =<< getII
--   case res of
--     Just (ii, _) -> do
--       printM 1 ("eliminateII: " <> prettyStr f)
--       -- TODO replace any II(e) where e is provably in `k`th segment.
--       -- For now, just replace II(i).
--       cs <- astMap (identityMapper {mapOnSymbol = repII ii}) (body f)
--       pure (f {body = cs})
--     Nothing -> pure f
--   where
--     repII vn (Apply (Var x) [arg])
--       | vn == x,
--         arg == sym2SoP (Var i) =
--           pure (Var k)
--     repII _ e = pure e
-- eliminateII f = pure f

{-
              Substitution rules
-}
-- -- Substitute `f(args)` for its value in `g`.
substituteOnce :: IndexFn -> IndexFn -> (Symbol, [SoP Symbol]) -> IndexFnM (Maybe IndexFn)
substituteOnce f g_presub (f_apply, actual_args) = do
  vn <- newVName ("<" <> prettyString f_apply <> ">")
  g <- repApply vn g_presub

  when shouldDebugSubst $
    printM 3 $
      "substituteOnce enter"
        <> "\n  f_apply: " <> prettyStr f_apply
        <> "\n  actual_args: " <> prettyStr actual_args
        <> "\n  shape f: " <> prettyStr (shape f)
        <> "\n  shape g_presub: " <> prettyStr (shape g_presub)

  when shouldDebugSubst $
    printM 3 $
      "substituteOnce args shape info"
        <> "\n  rank f: " <> prettyStr (rank f)
        <> "\n  length actual_args: " <> prettyStr (length actual_args)
        <> "\n  iterator count in shape f: " <> prettyStr (length (concat (shape f)))

  when shouldDebugSubst $
    printM 3 $ "--- f ---" <> prettyStr (f)
  when shouldDebugSubst $
    printM 3 $ "--- g ---" <> prettyStr (g)

  args <- mkArgs

  when shouldDebugSubst $
    printM 3 $
      "substituteOnce args replacement"
        <> "\n  args: " <> prettyStr args

  let new_shape =
        shape g
          <&> map
            ( \case
                Forall j dg
                  | vn `notElem` fv dg ->
                      Forall j dg
                  | Just e_f <- justSingleCase f ->
                      Forall j $ repDomain (mkRep vn (rep args e_f)) dg
                  | e_f <- flattenCases (body f) ->
                      Forall j $ repDomain (mkRep vn (rep args e_f)) dg
            )

  let g_sub =
        g
          { shape = new_shape,
            body = cases $ do
              (p_f, e_f) <- guards f
              (p_g, e_g) <- guards g
              let s = mkRep vn (rep args e_f)
              pure (sop2Symbol (rep s p_g) :&& sop2Symbol (rep args p_f), rep s e_g)
          }

  when shouldDebugSubst $
    printM 3 $
      "substituteOnce after building g_sub"
        <> "\n  new_shape: " <> prettyStr new_shape
        <> "\n  g_sub shape: " <> prettyStr (shape g_sub)
        <> "\n  g_sub body: " <> prettyStr (body g_sub)

  mg1 <- applySubRules args g_sub

  when shouldDebugSubst $
    printM 3 $
      "substituteOnce after applySubRules"
        <> "\n  mg1 shape: " <> prettyStr (shape <$> mg1)
      <> "\n  mg1 body: " <> prettyStr (body <$> mg1)

  mg2 <- case mg1 of
    Nothing ->
      pure Nothing
    Just g1 -> do
      -- printM 3 $ "substituteOnce actual shape after applySubRules=" <> prettyStr (shape g1)
      Just <$> solveIx (shape g1) g1

  -- printM 3 "substituteOnce after solveIx"
  -- print the domain
  printM 3 $ "substituteOnce domain after solveIx=" <> prettyStr (shape <$> mg2)
  printM 3 $ "substituteOnce body after solveIx=" <> prettyStr (body <$> mg2)

  mg3 <- traverse simplify mg2
  -- printM 3 "substituteOnce after simplify"

  mg3' <- traverse cleanupIndexFnM mg3
  
  pure mg3'
  where
    shouldDebugSubst :: Bool
    shouldDebugSubst =
      any (`isInfixOf` prettyString f_apply)
        [ "indsT"
        , "tmp"
        , "lst"
        , "seg_starts"
        , "ends"
        , "#f"
        ]

    cleanupIndexFnM :: IndexFn -> IndexFnM IndexFn
    cleanupIndexFnM g0 = do
      body_solved <- solveCasesUnderGuards (shape g0) (body g0)
      pure g0 {body = cleanupCases body_solved}

    cleanupCases :: Cases Symbol (SoP Symbol) -> Cases Symbol (SoP Symbol)
    cleanupCases (Cases cs) =
      Cases . NE.fromList $ dedup kept
      where
        xs = NE.toList cs

        -- remove impossible branches
        live = filter ((/= Bool False) . fst) xs

        -- Cases must stay non-empty, so if everything is dead,
        -- keep one original branch as a fallback
        kept =
          case live of
            [] -> take 1 xs
            _ -> live

        dedup = nubBy sameBranch

        sameBranch (p1, e1) (p2, e2) =
          p1 == p2 && e1 == e2

    solveCasesUnderGuards :: [[Quantified Domain]] -> Cases Symbol (SoP Symbol) -> IndexFnM (Cases Symbol (SoP Symbol))
    solveCasesUnderGuards shp (Cases cs) = do
      cs' <- mapM solveOneCase (NE.toList cs)
      pure $ Cases (NE.fromList cs')
      where
        solveOneCase (p, e)
          | p == Bool False =
              pure (p, e)
          | otherwise =
              rollbackAlgEnv $ do
                -- add the array/domain iterators, for example:
                -- i < m, j < shape[i]
                addRelShape shp

                -- this is the important part:
                -- while simplifying this branch, assume its guard is true.
                -- for example, in the second lst branch we know shape[i] /= 0.
                when (p /= Bool True) $
                  addRelSymbol p

                e' <- solveIx shp e
                pure (p, e')

    -- Construct replacement from formal arguments of f to actual arguments.
    mkArgs :: IndexFnM (Replacement Symbol)
    mkArgs =
      case actual_args of
        []
          | [] <- shape f -> pure mempty
          | [] <- shape g_presub -> pure mempty
          | rank f == rank g_presub
          , map length (shape f) == map length (shape g_presub) ->
              pure $
                mconcat $
                  zipWith
                    (\(Forall i _) a -> mkRep i a)
                    (concat (shape f))
                    (concat (shape g_presub) <&> sym2SoP . Var . boundVar)

        _
          | length actual_args == length (concat (shape f)) ->
              pure $
                mconcat $
                  zipWith
                    (\(Forall i _) a -> mkRep i a)
                    (concat (shape f))
                    actual_args

          | rank f == length actual_args -> do
              printM 3 $
                "mkArgs rank-based branch"
                  <> "\n  shape f: " <> prettyStr (shape f)
                  <> "\n  actual_args: " <> prettyStr actual_args

              reps <- zipWithM mkArgM (shape f) actual_args

              printM 3 $
                "mkArgs rank-based result"
                  <> "\n  reps: " <> prettyStr reps

              pure $ mconcat reps

          | otherwise ->
              error "Argument mismatch."

    mkArgM [Forall i _] a =
      pure $ mkRep i a

    mkArgM [d1, d2] a =
      mkRepFromList <$> from1Dto2DM d1 d2 a

    mkArgM _ _ =
      error "nd flatten not implemented yet."

    repApply vn =
      astMap
        ( identityMapper
            { mapOnSymbol = \e ->
                pure $ if e == f_apply then Var vn else e
            }
        )

    -- Side condition for Sub 2 and Sub 3:
    -- If f has a segmented domain, is f(arg) inside the k'th segment?
    arg_in_segment_of_f args n = case (shape f !! n, shape g_presub !! n) of
      ([Forall i df], [Forall j _]) -> do
        let arg_eq_j = pure . answerFromBool $ args M.! i == sym2SoP (Var j)
        let bounds e = intervalStart df :<= e :&& e :<= intervalEnd df
        let arg_in_segment_bounds =
              askQ
                (CaseCheck (\_ -> bounds $ args M.! i))
                g_presub
        arg_eq_j `orM` arg_in_segment_bounds
      _ -> error "Not implemented yet (arg_in_segment_of_f on non-1d or non-flat regular dimension)"

    -- Apply first matching rule for each dimension in f.
    applySubRules args g =
      runMaybeT $
        if null (shape g)
          then subRules args g 0
          else foldM (subRules args) g [0 .. rank f - 1]

    subRules args g n =
      sub0 g
        <|> MaybeT (propFlattenOnce n g f)
        <|> sub1 n g
        -- <|> sub2 n g
        -- <|> sub3 n g
        -- <|> sub4 n g
        -- <|> subX n g
      where
        -- args is currently only used by arg_in_segment_of_f in the old Cat rules
        -- keeping it in the signature so it is easy to re-enable those rules safely
        _ = arg_in_segment_of_f args

    -- This is rule is needed because we represent scalars as empty shapes rather
    -- than `for i < 1`, as is done in the paper.
    sub0 g = case shape f of
      [] -> pure g
      _ -> fail "No match."

    sub1 n g =
      if all (\case (Forall _ Iota {}) -> True; _ -> False) (shape f !! n)
        then pure g
        else fail "No match."

{-
              Utilities
-}
-- Solve for x in e(x) = e'.
solveFor :: VName -> SoP Symbol -> SoP Symbol -> IndexFnM (Maybe (SoP Symbol))
solveFor x e1 e2 = do
  x_hole <- newVName "x_hole"
  -- (Not using mkRep because this has check disallowing Holes.)
  let e1' = rep (M.singleton x $ sym2SoP (Hole x_hole)) e1
  s :: Maybe (Replacement Symbol) <- fmap mapping <$> unify e1' e2
  pure $ s >>= (M.!? x_hole)

firstAlt :: (Monad f) => [f (Maybe (SoP Symbol))] -> f (Maybe (SoP Symbol))
firstAlt [] = pure Nothing
firstAlt (m : ms) = do
  x <- m
  case x of
    Just y -> pure (Just y)
    Nothing -> firstAlt ms

gray :: String -> String
gray s = "\ESC[2m" <> s <> "\ESC[0m"
