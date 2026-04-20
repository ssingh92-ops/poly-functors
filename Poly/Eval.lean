/-
============================================================
Poly Project
File: Poly/Eval.lean
============================================================

## Purpose
This file makes precise that each polynomial/container P determines an
endofunctor on Type:

  evalFunctor(P) : Type ⥤ Type
  X ↦ P(X) = Σ a, (B a → X)

and it proves the functor laws:
  map_id, map_comp

## Why this matters
The book’s “polynomial functors” live as actual functors Set → Set (or Type → Type).
So we want:
  • object-level meaning (already: `eval`)
  • functoriality in X (this file)
  • naturality wrt morphisms between polynomials (later file: Semantics)

## What a non-Lean reader can ignore
The `map_id`/`map_comp` proofs are just “function extensionality + cases”
and are not mathematically deep.

============================================================
-/
import Poly.Core

universe u v w
open CategoryTheory

namespace PolyC

/--
Given a function h : X → Y, we can push a P-structure on X forward to Y
by applying h to every filled slot.

This is the standard “map” of the functor P(−).
-/
def evalMap (P : PolyC.{u, v}) {X Y : Type w} (h : X → Y) :
    P.eval X → P.eval Y
  | ⟨a, fill⟩ => ⟨a, fun p => h (fill p)⟩

/--
Evaluation as a functor:
  evalFunctor(P) : Type ⥤ Type
-/
def evalFunctor (P : PolyC.{u, v}) : Type w ⥤ Type (max u v w) where
  obj X := P.eval X
  map {X Y} h := evalMap P h
  map_id := by
    intro X
    funext x
    cases x
    rfl
  map_comp := by
    intro X Y Z f g
    funext x
    cases x
    rfl

/--
Naturality of `PolyC.map` with respect to changing the input type X.

This says:
If we first transport fillings X → Y and then apply a polynomial morphism,
it equals:
first apply the polynomial morphism and then transport fillings.

This is exactly the “naturality square” you want if you’re thinking
in terms of natural transformations.
-/
theorem map_natural {P Q : PolyC.{u, v}} (f : Hom P Q) {X Y : Type w} (h : X → Y) :
    (evalMap Q h) ∘ (map f) = (map f) ∘ (evalMap P h) := by
  funext x
  cases x with
  | mk a fill => rfl

end PolyC
