/-
============================================================
EE598 — Poly Project
File: Poly/SumProd.lean
============================================================

## Purpose
Define coproduct-like and product-like operations on polynomials and show
their evaluation behaves as expected.

(1) Sum:
  (P + Q).A := P.A ⊔ Q.A
  (P + Q).B := positions inherited from the chosen side

Then:
  (P + Q)(X) ≃ P(X) ⊔ Q(X)

(2) Product (cartesian product of polynomials):
  (P × Q).A := P.A × Q.A
  positions are a disjoint union:
    (P × Q).B(a,b) := P.B a ⊔ Q.B b

Then:
  (P × Q)(X) ≃ P(X) × Q(X)

## Why product positions are a Sum
This is a “choose whether the slot belongs to P or to Q.”
Filling all slots of the product means:
- fill P-slots with X
- fill Q-slots with X
which is exactly the data of a pair of fillings.

## What we prove here
We prove evaluation equivalences (≃) which are computationally explicit.
Later, we can upgrade these into universal properties inside the category PolyC.

============================================================
-/
import Poly.Core

universe u v w

namespace PolyC

def sum (P Q : PolyC.{u, v}) : PolyC.{u, v} where
  A := Sum P.A Q.A
  B := fun s =>
    match s with
    | Sum.inl a => P.B a
    | Sum.inr b => Q.B b

def prod (P Q : PolyC.{u, v}) : PolyC.{u, v} where
  A := P.A × Q.A
  B := fun ab => Sum (P.B ab.1) (Q.B ab.2)

/-- Explicit equivalence: (P + Q)(X) ≃ P(X) ⊔ Q(X). -/
def evalSumEquiv (P Q : PolyC.{u, v}) (X : Type w) :
    (sum P Q).eval X ≃ Sum (P.eval X) (Q.eval X) where
  toFun
    | ⟨Sum.inl a, fill⟩ => Sum.inl ⟨a, fill⟩
    | ⟨Sum.inr b, fill⟩ => Sum.inr ⟨b, fill⟩
  invFun
    | Sum.inl ⟨a, fill⟩ => ⟨Sum.inl a, fill⟩
    | Sum.inr ⟨b, fill⟩ => ⟨Sum.inr b, fill⟩
  left_inv := by
    intro x
    cases x with
    | mk s fill =>
      cases s <;> rfl
  right_inv := by
    intro y
    cases y <;> rfl

/-- Explicit equivalence: (P × Q)(X) ≃ P(X) × Q(X). -/
def evalProdEquiv (P Q : PolyC.{u, v}) (X : Type w) :
    (prod P Q).eval X ≃ (P.eval X × Q.eval X) where
  toFun
    | ⟨⟨a, b⟩, fill⟩ =>
      (⟨a, fun pa => fill (Sum.inl pa)⟩, ⟨b, fun qb => fill (Sum.inr qb)⟩)
  invFun
    | (⟨a, fillA⟩, ⟨b, fillB⟩) =>
      ⟨⟨a, b⟩, fun s => Sum.casesOn s fillA fillB⟩
  left_inv := by
    intro x
    cases x with
    | mk ab fill =>
      cases ab with
      | mk a b =>
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext s
          cases s <;> rfl
  right_inv := by
    rintro ⟨⟨a, fillA⟩, ⟨b, fillB⟩⟩
    rfl

end PolyC
