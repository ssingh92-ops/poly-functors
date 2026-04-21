/-
============================================================
File: Poly.lean
============================================================

This is the one import a reader should use:

It pulls in:
- Core container definition + category
- Evaluation functor in X
- Semantics embedding into (Type ⥤ Type)
- Sum/product and composition formulas
- Bridge to Mathlib PFunctor
- Examples
- Universal properties of sums/products
- Parallel composition and distributivity
- CompMonoidal structure
- CompOnMorphisms structure
- Composition semantics
- Equalizers and their semantics

Dependency graph:
  Core → Eval → Semantics
  Core → SumProd
  Core → Composition
  Core → PFunctorBridge
  Core → Examples

============================================================
-/
import Poly.Core
import Poly.Eval
import Poly.Semantics

import Poly.SumProd
import Poly.Universal

import Poly.Composition
import Poly.CompOnMorphisms
import Poly.CompSemantics
import Poly.CompMonoidal
import Poly.CompositionProducts
import Poly.CompositionExamples
import Poly.CompositionInteractions

import Poly.Parallel
import Poly.ParallelDistribute

import Poly.PFunctorBridge
import Poly.Examples

import Poly.Equalizers
import Poly.SemanticEqualizers

import Poly.Pullbacks
import Poly.SemanticPullbacks
import Poly.PullbackPositionsDirections

import Poly.IndexedProducts
import Poly.IndexedCoproducts

import Poly.FiniteLimits
import Poly.SmallLimits

import Poly.PositionsDirections

import Poly.Coequalizers
import Poly.SmallColimits

import Poly.Terminology
