/-
============================================================
EE598 — Poly Project
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
import Poly.Composition
import Poly.PFunctorBridge
import Poly.Examples
import Poly.Universal
import Poly.Parallel
import Poly.ParallelDistribute
import Poly.CompMonoidal
import Poly.CompOnMorphisms
import Poly.Composition
import Poly.CompSemantics
import Poly.PFunctorBridge
