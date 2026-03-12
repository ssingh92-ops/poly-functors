/-
============================================================
EE598 — Poly Project
File: Poly/Core.lean
============================================================

## Purpose
This file defines what we mean by a *polynomial functor* in the “container”
sense, and it defines the category structure on them.

A polynomial/container is data:

  P = (A, B)
  • A : Type        = shapes (think: constructors / blueprints)
  • B : A → Type    = positions for each shape (slots to fill)

Its Type-level semantics on an input type X is:

  P(X) := Σ a : A, (B a → X)

Read it as:
  "choose a shape a, then give an X-label for each position in B a."

## Purpose (Lean-readable)
We implement:
  - `structure PolyC`  with fields `A` and `B`
  - `def eval`         implementing P(X)
  - `structure Hom`    implementing container morphisms (dependent lenses)
  - `def map`          induced function on semantics
  - `instance : Category PolyC` (identity + composition + laws)

## Morphisms (lens intuition)
A morphism f : P ⟶ Q is:

  f.onShapes : P.A → Q.A                     (forward on shapes)
  f.onPos    : ∀ a, Q.B (f.onShapes a) → P.B a  (backward on positions)

Why backward on positions?
Because given a Q-filling, we want to pull it back to a P-filling by
precomposition.

## What a non-Lean reader can ignore
The `Hom.ext` lemma and the `Category` proofs are “plumbing.”
They are short because the definitions were chosen so that the laws hold
by definitional equality (`rfl`).

============================================================
-/
import Mathlib

universe u v w
open CategoryTheory

/-- Container polynomial: shapes `A` and positions `B : A → Type`. -/
structure PolyC where
  A : Type u
  B : A → Type v

namespace PolyC

/--
Type-level semantics (evaluation) of a container polynomial:

  eval P X = Σ a : P.A, (P.B a → X)

This is the standard container semantics:
  ∑_{a∈A} X^{B(a)}
where `X^{B(a)}` is implemented as functions `B a → X`.
-/
def eval (P : PolyC.{u, v}) (X : Type w) : Type (max u v w) :=
  Sigma (fun a : P.A => (P.B a → X))

/--
A morphism of container polynomials (a dependent lens):

  P ⟶ Q  consists of:
  • onShapes : P.A → Q.A
  • onPos    : ∀ a, Q.B (onShapes a) → P.B a

Interpretation:
- send each source shape forward to a target shape
- pull target positions back to source positions
-/
structure Hom (P Q : PolyC.{u, v}) where
  onShapes : P.A → Q.A
  onPos    : ∀ a : P.A, Q.B (onShapes a) → P.B a

/-- Identity morphism: shapes map to themselves, positions map to themselves. -/
def id (P : PolyC.{u, v}) : Hom P P where
  onShapes := fun a => a
  onPos    := fun _ p => p

/--
Composition of container morphisms.

If f : P ⟶ Q and g : Q ⟶ R, then g ∘ f : P ⟶ R:

- shapes: a ↦ g.onShapes (f.onShapes a)
- positions: pull back twice
-/
def comp {P Q R : PolyC.{u, v}} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  onShapes := fun a => g.onShapes (f.onShapes a)
  onPos := fun a rpos => f.onPos a (g.onPos (f.onShapes a) rpos)

/--
Action of a morphism on semantics (the “meaning-preserving map”).

Given f : P ⟶ Q and a filled P-structure (a, fillP),
we produce a filled Q-structure:

  (f.onShapes a, fillQ)
where:
  fillQ(qpos) := fillP(f.onPos a qpos)

So we fill Q-positions by pulling them back to P-positions.
-/
def map {P Q : PolyC.{u, v}} (f : Hom P Q) {X : Type w} :
    P.eval X → Q.eval X
  | ⟨a, fillP⟩ =>
      ⟨f.onShapes a, fun qpos => fillP (f.onPos a qpos)⟩

/--
Extensionality for morphisms.
Two morphisms are equal if their shape maps are equal and their position maps
are (heterogeneously) equal pointwise.

This lemma is useful when we later build isomorphisms in PolyC
(unitors/associators/braidings).
-/
@[ext (iff := false)]
lemma Hom.ext {P Q : PolyC.{u, v}} (f g : Hom P Q)
    (hShapes : f.onShapes = g.onShapes)
    (hPos : ∀ a : P.A, HEq (f.onPos a) (g.onPos a)) : f = g := by
  cases f with
  | mk fShapes fPos =>
    cases g with
    | mk gShapes gPos =>
      cases hShapes
      have : fPos = gPos := by
        funext a
        exact eq_of_heq (hPos a)
      cases this
      rfl

/--
Category instance on PolyC.

Why the proofs are `rfl`:
- Our `id` and `comp` were defined exactly like function composition,
  so the category laws are definitional equalities.
-/
instance : Category PolyC.{u, v} where
  Hom P Q := Hom P Q
  id P := id P
  comp f g := comp f g
  id_comp := by
    intro X Y f
    rfl
  comp_id := by
    intro X Y f
    rfl
  assoc := by
    intro W X Y Z f g h
    rfl

end PolyC
