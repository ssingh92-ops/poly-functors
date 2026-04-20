/-
============================================================
Poly Project
File: Poly/CompOnMorphisms.lean
============================================================

## Goal
We already defined composition/substitution on objects:

  composeObj P Q

with semantics:
  (composeObj P Q)(X) ≃ P(Q(X))

Milestone 6 requires the hard part:
- define how composition acts on morphisms (lenses)
- package this into a functor on the product category

In other words:
  (P ⟶ P') and (Q ⟶ Q')
should induce:
  (P ▷ Q) ⟶ (P' ▷ Q')

This is a “bifunctor on morphisms”.

## High-level idea
A shape of (P ▷ Q) is:
  (a : P.A, k : P.B a → Q.A)

Given f : P ⟶ P' and g : Q ⟶ Q',
we map the outer shape forward by f, and map each chosen inner Q-shape forward by g.

But because lens morphisms pull positions backward, the inner map uses `f.onPos`
to translate a P'-position back to a P-position before looking up k.

============================================================
-/
import Poly.Composition

universe u v
open CategoryTheory

namespace PolyC

/-- Notation for composition/substitution on objects. -/
infixr:80 " ▷ " => composeObj

/--
Composition on morphisms.

Given:
  f : P ⟶ P'
  g : Q ⟶ Q'

produce:
  (f ▷ g) : (P ▷ Q) ⟶ (P' ▷ Q')
-/
def composeHom {P P' Q Q' : PolyC.{u, v}} (f : P ⟶ P') (g : Q ⟶ Q') :
    (P ▷ Q) ⟶ (P' ▷ Q') where
  onShapes := fun s =>
    -- s : Σ a : P.A, (P.B a → Q.A)
    -- output: Σ a' : P'.A, (P'.B a' → Q'.A)
    ⟨ f.onShapes s.1
    , fun p' => g.onShapes (s.2 (f.onPos s.1 p')) ⟩
  onPos := fun s d =>
    -- d : Σ p' : P'.B (f.onShapes s.1), Q'.B (g.onShapes (s.2 (f.onPos s.1 p')))
    -- map back to Σ p : P.B s.1, Q.B (s.2 p)
    let p : P.B s.1 := f.onPos s.1 d.1
    ⟨ p, g.onPos (s.2 p) d.2 ⟩

/--
Bifunctor form:
  (P,Q) ↦ P ▷ Q
  (f,g) ↦ composeHom f g
-/
def compBifunctor : (PolyC.{u, v} × PolyC.{u, v}) ⥤ PolyC.{max u v, v} where
  obj PQ := (PQ.1 ▷ PQ.2)
  map {PQ PQ'} fg := composeHom (P := PQ.1) (P' := PQ'.1) (Q := PQ.2) (Q' := PQ'.2) fg.1 fg.2
  map_id := by
    intro PQ
    cases PQ with
    | mk P Q =>
      apply Hom.ext
      · funext s
        cases s with
        | mk a k =>
          rfl
      · intro s
        apply heq_of_eq
        funext d
        cases s with
        | mk a k =>
          cases d with
          | mk p' q'pos =>
            rfl
  map_comp := by
    intro X Y Z f g
    -- f : X ⟶ Y is a pair (f.1, f.2); g similarly.
    -- We show: composeHom (f≫g) = composeHom f ≫ composeHom g
    apply Hom.ext
    · funext s
      cases s with
      | mk a k =>
        rfl
    · intro s
      apply heq_of_eq
      funext d
      cases s with
      | mk a k =>
        cases d with
        | mk p' q'pos =>
          rfl

end PolyC
