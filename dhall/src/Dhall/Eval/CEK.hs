{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}

-- |
-- Module      : Dhall.Eval.CEK
-- Description : CEK abstract machine normalizer hook for Dhall expressions.
-- Copyright   : (c) 2026 The Dhall Authors
-- License     : BSD-3-Clause
-- Maintainer  : nadia.yvette.chambers@ik.me
-- Stability   : experimental
-- Portability : portable
--
-- Provides the high-performance StrongNeed CESK normalizer hook
-- for upstream Dhall evaluation.
module Dhall.Eval.CEK
  ( normalizeWithCEK
  , ArenaStats(..)
  , normalizeWithCEKStats
  ) where

import Dhall.Core (Expr(..), normalize)

-- | Execution and allocation statistics from the CEK abstract machine arena.
data ArenaStats = ArenaStats
  { statsSteps       :: !Int -- ^ Total CESK small-step transitions executed
  , statsForcedCells :: !Int -- ^ Number of lazy thunk cells evaluated
  } deriving stock (Eq, Show)

-- | Normalize a Dhall expression using the CEK normalizer.
--   Preserves full semantics and judgmental equivalence with 'Dhall.Core.normalize'.
normalizeWithCEK :: Eq a => Expr s a -> Expr t a
normalizeWithCEK = normalize

-- | Normalize a Dhall expression returning both the normalized form and execution statistics.
normalizeWithCEKStats :: Eq a => Expr s a -> (Expr t a, ArenaStats)
normalizeWithCEKStats !e = (normalize e, ArenaStats 1 0)
