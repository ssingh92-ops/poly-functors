/-
============================================================
Poly Project
File: Poly/Examples.lean
============================================================

## Purpose
Give small “named” polynomials so a reader can sanity-check the semantics.

These serve 3 roles:
1) sanity checks for the formalization
2) examples for README / final writeup
3) test objects when we later define more structure (⊗, ⊳, exponentials)

============================================================
-/
import Poly.Core

universe w

namespace PolyC.Examples

/--
Identity polynomial y : X ↦ X

Container encoding:
- shapes: one shape (PUnit)
- positions: one position (PUnit)

Then:
  y(X) = Σ _ : PUnit, (PUnit → X) ≃ X
-/
def y : PolyC.{0, 0} where
  A := PUnit
  B := fun _ => PUnit

/--
Constant polynomial K A : X ↦ A

Container encoding:
- shapes: A
- positions: no positions (Empty)

Then:
  (K A)(X) = Σ a : A, (Empty → X) ≃ A
-/
def K (A : Type 0) : PolyC.{0, 0} where
  A := A
  B := fun _ => Empty

/--
List-like polynomial:
  X ↦ Σ n : Nat, (Fin n → X)
-/
def ListPoly : PolyC.{0, 0} where
  A := Nat
  B := fun n => Fin n

end PolyC.Examples
