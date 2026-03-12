/-
============================================================
EE598 — Poly Project
File: Poly/Parallel.lean
============================================================

## What this file adds (book-level structure)
This file defines the *parallel product* of polynomials, written ⊗.

This is NOT the categorical product of functors.
- Functor product corresponds to pairing outputs, and in container form it
  uses a SUM of position-sets (what we called `prod` in SumProd.lean).

The parallel product ⊗ is different: it multiplies the direction-sets.

Book intuition (informal):
- You have two interactive systems running "in parallel".
- A move/direction in the composite system is a PAIR of moves
  (one move from each subsystem).

Container formula:

  If P = (A, B) and Q = (C, D), then

    (P ⊗ Q).A := A × C
    (P ⊗ Q).B (a, c) := B a × D c

So shapes pair, and directions pair.

## What we implement
1) The object-level definition `tensor` (notation ⊗).
2) The morphism-level action `tensorHom` (componentwise on shapes/positions).
3) The standard coherence isomorphisms:
   - left/right unitors using y
   - associator
   - braiding (symmetry)

These are the starting pieces for showing PolyC has a symmetric monoidal
structure under ⊗ (the “Dirichlet/parallel” monoidal structure).

============================================================
-/
import Poly.Core

universe u v
open CategoryTheory

namespace PolyC

/--
The “y” polynomial (the basic one-position container).

It acts as a unit for ⊗:
  y ⊗ P ≅ P   and   P ⊗ y ≅ P

Container:
  y.A = PUnit
  y.B(*) = PUnit
So y(X) = Σ _ : 1, (1 → X) ≃ X.
-/
def y : PolyC.{u, v} where
  A := PUnit
  B := fun _ => PUnit

/--
Parallel / Dirichlet product of polynomials (notation ⊗).

Shapes pair.
Directions pair.
-/
def tensor (P Q : PolyC.{u, v}) : PolyC.{u, v} where
  A := P.A × Q.A
  B := fun ab => P.B ab.1 × Q.B ab.2

infixl:70 " ⊗ " => tensor

/--
⊗ on morphisms (componentwise):

If f : P ⟶ P' and g : Q ⟶ Q', then
  f ⊗ g : (P ⊗ Q) ⟶ (P' ⊗ Q')
-/
def tensorHom {P P' Q Q' : PolyC.{u, v}} (f : P ⟶ P') (g : Q ⟶ Q') :
    (P ⊗ Q) ⟶ (P' ⊗ Q') where
  onShapes := fun ab => (f.onShapes ab.1, g.onShapes ab.2)
  onPos := fun ab d =>
    (f.onPos ab.1 d.1, g.onPos ab.2 d.2)

/-
============================================================
Coherence isomorphisms for ⊗
============================================================
-/

/-- Left unitor: y ⊗ P ≅ P. -/
def tensorLeftUnitor (P : PolyC.{u, v}) : (y ⊗ P) ≅ P where
  hom :=
    { onShapes := fun ap => ap.2
      onPos := fun ap pb => (PUnit.unit, pb) }
  inv :=
    { onShapes := fun a => (PUnit.unit, a)
      onPos := fun a d => d.2 }
  hom_inv_id := by
    apply Hom.ext
    · funext ap
      cases ap with
      | mk u a =>
        cases u
        rfl
    · intro ap
      apply heq_of_eq
      funext d
      cases ap with
      | mk u a =>
        cases u
        cases d with
        | mk uu pb =>
          cases uu
          rfl
  inv_hom_id := by
    apply Hom.ext
    · funext a
      rfl
    · intro a
      apply heq_of_eq
      funext pb
      rfl

/-- Right unitor: P ⊗ y ≅ P. -/
def tensorRightUnitor (P : PolyC.{u, v}) : (P ⊗ y) ≅ P where
  hom :=
    { onShapes := fun au => au.1
      onPos := fun au pb => (pb, PUnit.unit) }
  inv :=
    { onShapes := fun a => (a, PUnit.unit)
      onPos := fun a d => d.1 }
  hom_inv_id := by
    apply Hom.ext
    · funext au
      cases au with
      | mk a u =>
        cases u
        rfl
    · intro au
      apply heq_of_eq
      funext d
      cases au with
      | mk a u =>
        cases u
        cases d with
        | mk pb uu =>
          cases uu
          rfl
  inv_hom_id := by
    apply Hom.ext
    · funext a
      rfl
    · intro a
      apply heq_of_eq
      funext pb
      rfl

/-- Associator: (P ⊗ Q) ⊗ R ≅ P ⊗ (Q ⊗ R). -/
def tensorAssociator (P Q R : PolyC.{u, v}) :
    ((P ⊗ Q) ⊗ R) ≅ (P ⊗ (Q ⊗ R)) where
  hom :=
    { onShapes := fun s => (s.1.1, (s.1.2, s.2))
      onPos := fun s d =>
        -- target directions: P.B a × (Q.B b × R.B c)
        -- source directions: (P.B a × Q.B b) × R.B c
        ((d.1, d.2.1), d.2.2) }
  inv :=
    { onShapes := fun s => ((s.1, s.2.1), s.2.2)
      onPos := fun s d =>
        -- target directions: (P.B a × Q.B b) × R.B c
        -- source directions: P.B a × (Q.B b × R.B c)
        (d.1.1, (d.1.2, d.2)) }
  hom_inv_id := by
    apply Hom.ext
    · funext s
      cases s with
      | mk pq c =>
        cases pq with
        | mk a b =>
          rfl
    · intro s
      apply heq_of_eq
      funext d
      cases d with
      | mk pq rc =>
        cases pq with
        | mk pa qb =>
          rfl
  inv_hom_id := by
    apply Hom.ext
    · funext s
      cases s with
      | mk a bc =>
        cases bc with
        | mk b c =>
          rfl
    · intro s
      apply heq_of_eq
      funext d
      cases d with
      | mk pa qrc =>
        cases qrc with
        | mk qb rc =>
          rfl

/-- Braiding (symmetry): P ⊗ Q ≅ Q ⊗ P. -/
def tensorBraiding (P Q : PolyC.{u, v}) : (P ⊗ Q) ≅ (Q ⊗ P) where
  hom :=
    { onShapes := fun ab => (ab.2, ab.1)
      onPos := fun ab d => (d.2, d.1) }
  inv :=
    { onShapes := fun ba => (ba.2, ba.1)
      onPos := fun ba d => (d.2, d.1) }
  hom_inv_id := by
    apply Hom.ext
    · funext ab
      rfl
    · intro ab
      apply heq_of_eq
      funext d
      cases d
      rfl
  inv_hom_id := by
    apply Hom.ext
    · funext ba
      rfl
    · intro ba
      apply heq_of_eq
      funext d
      cases d
      rfl

end PolyC
