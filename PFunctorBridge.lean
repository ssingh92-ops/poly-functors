/-
============================================================
EE598 — Poly Project
File: Poly/PFunctorBridge.lean
============================================================

## Purpose
Mathlib already has the “container” idea as `PFunctor` (univariate polynomial functor).
This file gives a *direct translation* between our `PolyC` and Mathlib’s `PFunctor`.

Why do this?
- It shows our definitions are not made up — they align with existing Mathlib structures.
- It lets us reuse library facts about `PFunctor` later if we want.
- It provides a credibility anchor for readers familiar with Mathlib.

Important note:
We are NOT claiming Mathlib’s entire “Polynomial functor” category exists already.
We are just showing that at the data level, `PolyC` matches `PFunctor`.

============================================================
-/
import Poly.Core
import Mathlib.Data.PFunctor.Univariate.Basic

universe u v w

namespace PolyC

def toPFunctor (P : PolyC.{u, v}) : PFunctor.{u, v} where
  A := P.A
  B := P.B

def ofPFunctor (P : PFunctor.{u, v}) : PolyC.{u, v} where
  A := P.A
  B := P.B

@[simp] lemma ofPFunctor_toPFunctor (P : PolyC.{u, v}) :
    ofPFunctor (toPFunctor P) = P := by
  cases P
  rfl

@[simp] lemma toPFunctor_ofPFunctor (P : PFunctor.{u, v}) :
    toPFunctor (ofPFunctor P) = P := by
  cases P
  rfl

/--
Explicit evaluation formula for Mathlib `PFunctor`.
We keep it here to avoid relying on field-name rewriting in proofs.
-/
def pfunctorObj (F : PFunctor.{u, v}) (X : Type w) : Type (max u v w) :=
  Sigma (fun a : F.A => (F.B a → X))

@[simp] lemma eval_eq_pfunctor_obj (P : PolyC.{u, v}) (X : Type w) :
    P.eval X = pfunctorObj (toPFunctor P) X := by
  rfl

end PolyC
