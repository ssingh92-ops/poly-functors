import Poly.Core

/-
============================================================
Poly Project
File: Poly/Terminology.lean
============================================================

This file provides book-facing terminology for the core `PolyC` API.

The original core file uses older internal field names:

  • `A`
  • `B`
  • `onShapes`
  • `onPos`

Mathematically, and in the book-facing presentation, these should be read as:

  • `A`        = positions,
  • `B a`      = directions at position `a`,
  • `onShapes` = forward map on positions,
  • `onPos`    = backward pullback map on directions.

This file does not change the underlying definitions. It gives aliases and
constructors so future files can be written using positions/directions
language without rewriting the already-working development.
============================================================
-/

open CategoryTheory

namespace PolyC

universe u v

/-
==============================================================================
Object-level terminology
==============================================================================
-/

/-- The type of positions of a polynomial functor. -/
abbrev positions (P : PolyC.{u, v}) : Type u :=
  P.A

/-- The type of directions at a given position. -/
abbrev directions (P : PolyC.{u, v}) (a : positions P) : Type v :=
  P.B a

/--
Build a polynomial functor from a type of positions and a family of direction
types.
-/
def ofPositionsDirections
    (Pos : Type u)
    (Dir : Pos → Type v) :
    PolyC.{u, v} where
  A := Pos
  B := Dir

@[simp] theorem positions_ofPositionsDirections
    (Pos : Type u) (Dir : Pos → Type v) :
    positions (ofPositionsDirections Pos Dir) = Pos := by
  rfl

@[simp] theorem directions_ofPositionsDirections
    (Pos : Type u) (Dir : Pos → Type v) (a : Pos) :
    directions (ofPositionsDirections Pos Dir) a = Dir a := by
  rfl

/-
==============================================================================
Morphism-level terminology
==============================================================================
-/

namespace Hom

/-- The forward map on positions of a polynomial morphism. -/
abbrev onPositions {P Q : PolyC.{u, v}} (f : P ⟶ Q) :
    positions P → positions Q :=
  f.onShapes

/--
The backward pullback map on directions of a polynomial morphism.

For `f : P ⟶ Q` and `a : positions P`, this sends directions of `Q` at the
image position `f.onPositions a` back to directions of `P` at `a`.
-/
abbrev onDirections {P Q : PolyC.{u, v}} (f : P ⟶ Q)
    (a : positions P) :
    directions Q (onPositions f a) → directions P a :=
  f.onPos a

/-- Alternative name emphasizing that directions are pulled back. -/
abbrev pullDirections {P Q : PolyC.{u, v}} (f : P ⟶ Q)
    (a : positions P) :
    directions Q (onPositions f a) → directions P a :=
  onDirections f a

@[simp] theorem onPositions_apply {P Q : PolyC.{u, v}}
    (f : P ⟶ Q) (a : positions P) :
    onPositions f a = f.onShapes a := by
  rfl

@[simp] theorem onDirections_apply {P Q : PolyC.{u, v}}
    (f : P ⟶ Q) (a : positions P)
    (d : directions Q (onPositions f a)) :
    onDirections f a d = f.onPos a d := by
  rfl

@[simp] theorem pullDirections_apply {P Q : PolyC.{u, v}}
    (f : P ⟶ Q) (a : positions P)
    (d : directions Q (onPositions f a)) :
    pullDirections f a d = f.onPos a d := by
  rfl

/--
Build a polynomial morphism from a forward map on positions and a backward map
on directions.
-/
def ofPositionsDirections {P Q : PolyC.{u, v}}
    (forwardPositions : positions P → positions Q)
    (backwardDirections :
      ∀ a : positions P,
        directions Q (forwardPositions a) → directions P a) :
    P ⟶ Q where
  onShapes := forwardPositions
  onPos := backwardDirections

@[simp] theorem ofPositionsDirections_onPositions {P Q : PolyC.{u, v}}
    (forwardPositions : positions P → positions Q)
    (backwardDirections :
      ∀ a : positions P,
        directions Q (forwardPositions a) → directions P a)
    (a : positions P) :
    onPositions (ofPositionsDirections forwardPositions backwardDirections) a
      =
    forwardPositions a := by
  rfl

@[simp] theorem ofPositionsDirections_onDirections {P Q : PolyC.{u, v}}
    (forwardPositions : positions P → positions Q)
    (backwardDirections :
      ∀ a : positions P,
        directions Q (forwardPositions a) → directions P a)
    (a : positions P)
    (d : directions Q (forwardPositions a)) :
    onDirections
        (ofPositionsDirections forwardPositions backwardDirections)
        a d
      =
    backwardDirections a d := by
  rfl

end Hom

end PolyC
