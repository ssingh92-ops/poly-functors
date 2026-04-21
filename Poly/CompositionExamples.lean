import Poly.Examples
import Poly.CompositionProducts

/-
============================================================
Poly Project
File: Poly/CompositionExamples.lean
============================================================

This file gives small examples for the Chapter 6 composition product.

The composition product is the monoidal operation on polynomial functors
given by substitution:

  (P ▷ Q)(X) ≃ P(Q(X)).

The core construction and theorem package live in:

  • `Poly/Composition.lean`,
  • `Poly/CompOnMorphisms.lean`,
  • `Poly/CompSemantics.lean`,
  • `Poly/CompMonodial.lean`,
  • `Poly/CompositionProduct.lean`.

This file does not construct new theory. It provides readable sanity checks
showing that the composition-product API can be used with the concrete
examples from `Poly/Examples.lean`.

Terminology note:
the core code still uses the internal field names

  • `A`        = positions,
  • `B a`      = directions at position `a`,
  • `onShapes` = forward map on positions,
  • `onPos`    = backward pullback map on directions.

The comments below use positions/directions.
============================================================
-/

open CategoryTheory

namespace PolyC.Examples

universe w

/-
==============================================================================
Basic composition-product examples
==============================================================================
-/

/--
The composition product `PairPoly ▷ MaybePoly`.

Semantically, this evaluates as

  PairPoly(MaybePoly(X)),

so it is equivalent to two independent `MaybePoly(X)` values.
-/
def PairOfMaybePoly : PolyC.{0, 0} :=
  compositionProduct PairPoly MaybePoly

/--
The composition product `ListPoly ▷ MaybePoly`.

Semantically, this evaluates as

  ListPoly(MaybePoly(X)),

so it is equivalent to length-indexed tuples of `MaybePoly(X)` values.
-/
def ListOfMaybePoly : PolyC.{0, 0} :=
  compositionProduct ListPoly MaybePoly

/--
The composition product `MaybePoly ▷ PairPoly`.

Semantically, this evaluates as

  MaybePoly(PairPoly(X)).
-/
def MaybeOfPairPoly : PolyC.{0, 0} :=
  compositionProduct MaybePoly PairPoly

/--
The composition product `PairPoly ▷ PairPoly`.

Semantically, this evaluates as

  PairPoly(PairPoly(X)),

so it is equivalent to a pair of pairs of elements of `X`.
-/
def PairOfPairPoly : PolyC.{0, 0} :=
  compositionProduct PairPoly PairPoly

/-
==============================================================================
Semantic substitution examples
==============================================================================
-/

/--
Semantic substitution for `PairPoly ▷ MaybePoly`.
-/
def evalPairOfMaybeEquiv (X : Type w) :
    PairOfMaybePoly.eval X ≃ PairPoly.eval (MaybePoly.eval X) :=
  compositionProductEvalEquiv PairPoly MaybePoly X

/--
A more concrete semantic normal form for `PairPoly ▷ MaybePoly`.

Since `PairPoly(Y) ≃ Y × Y`, this says

  (PairPoly ▷ MaybePoly)(X) ≃ MaybePoly(X) × MaybePoly(X).
-/
def evalPairOfMaybeAsPairEquiv (X : Type w) :
    PairOfMaybePoly.eval X ≃ (MaybePoly.eval X × MaybePoly.eval X) :=
  (compositionProductEvalEquiv PairPoly MaybePoly X).trans
    (evalPairEquiv (MaybePoly.eval X))

/--
Semantic substitution for `ListPoly ▷ MaybePoly`.
-/
def evalListOfMaybeEquiv (X : Type w) :
    ListOfMaybePoly.eval X ≃ ListPoly.eval (MaybePoly.eval X) :=
  compositionProductEvalEquiv ListPoly MaybePoly X

/--
A more concrete semantic normal form for `ListPoly ▷ MaybePoly`.

Since `ListPoly(Y) ≃ Σ n : Nat, Fin n → Y`, this says

  (ListPoly ▷ MaybePoly)(X) ≃ Σ n : Nat, Fin n → MaybePoly(X).
-/
def evalListOfMaybeAsTuplesEquiv (X : Type w) :
    ListOfMaybePoly.eval X ≃ Sigma (fun n : Nat => Fin n → MaybePoly.eval X) :=
  (compositionProductEvalEquiv ListPoly MaybePoly X).trans
    (evalListPolyEquiv (MaybePoly.eval X))

/--
Semantic substitution for `MaybePoly ▷ PairPoly`.
-/
def evalMaybeOfPairEquiv (X : Type w) :
    MaybeOfPairPoly.eval X ≃ MaybePoly.eval (PairPoly.eval X) :=
  compositionProductEvalEquiv MaybePoly PairPoly X

/--
Semantic substitution for `PairPoly ▷ PairPoly`.
-/
def evalPairOfPairEquiv (X : Type w) :
    PairOfPairPoly.eval X ≃ PairPoly.eval (PairPoly.eval X) :=
  compositionProductEvalEquiv PairPoly PairPoly X

/-
==============================================================================
Unit and associativity examples
==============================================================================

The composition-product unit is the variable polynomial `y`.

The project already has an example-local `y`, but the packaged composition
unit is `PolyC.y` from the core composition/monoidal layer. We use `PolyC.y`
below to match the unitors from `CompositionProduct.lean`.
-/

/-- Left unit law example: `y ▷ MaybePoly ≅ MaybePoly`. -/
def yCompMaybeIso :
    compositionProduct (PolyC.y.{0, 0}) MaybePoly ≅ MaybePoly :=
  compositionProductLeftUnitor MaybePoly

/-- Right unit law example: `MaybePoly ▷ y ≅ MaybePoly`. -/
def maybeCompYIso :
    compositionProduct MaybePoly (PolyC.y.{0, 0}) ≅ MaybePoly :=
  compositionProductRightUnitor MaybePoly

/--
Associativity example:

  (PairPoly ▷ MaybePoly) ▷ ListPoly
    ≅
  PairPoly ▷ (MaybePoly ▷ ListPoly).
-/
def compositionAssociatorExample :
    compositionProduct (compositionProduct PairPoly MaybePoly) ListPoly
      ≅
    compositionProduct PairPoly (compositionProduct MaybePoly ListPoly) :=
  compositionProductAssociator PairPoly MaybePoly ListPoly

/-
==============================================================================
Composition product on morphisms
==============================================================================

The composition product also acts on lenses/morphisms.
-/

/--
Apply `pairSwap` on the outer polynomial and the identity on the inner
polynomial.
-/
def pairSwapOnPairOfMaybe :
    PairOfMaybePoly ⟶ PairOfMaybePoly :=
  compositionProductMap pairSwap (𝟙 MaybePoly)

/--
Identity law for the composition-product action on morphisms.
-/
theorem compositionProductMap_id_example :
    compositionProductMap (𝟙 PairPoly) (𝟙 MaybePoly)
      =
    𝟙 PairOfMaybePoly := by
  exact compositionProductMap_id PairPoly MaybePoly

/--
Functoriality example for the composition-product action on morphisms.
-/
theorem compositionProductMap_comp_example :
    compositionProductMap
        (pairSwap ≫ pairSwap)
        ((𝟙 MaybePoly) ≫ (𝟙 MaybePoly))
      =
    compositionProductMap pairSwap (𝟙 MaybePoly)
      ≫
    compositionProductMap pairSwap (𝟙 MaybePoly) := by
  exact compositionProductMap_comp
    pairSwap pairSwap
    (𝟙 MaybePoly) (𝟙 MaybePoly)

/-
==============================================================================
Positions-and-directions examples
==============================================================================

These examples show that the composition product is included in the global
positions-and-directions theorem family.
-/

/--
Positions and directions of `PairPoly ▷ MaybePoly`.

Positions are composite positions, and directions are composite directions.
-/
theorem pairOfMaybe_positions_directions :
    Nonempty
      (PairOfMaybePoly.A
        ≃ Sigma (fun a : PairPoly.A => PairPoly.B a → MaybePoly.A))
      ∧
    (∀ s : PairOfMaybePoly.A,
      Nonempty
        (PairOfMaybePoly.B s
          ≃ Sigma (fun p : PairPoly.B s.1 => MaybePoly.B (s.2 p)))) := by
  exact compositionProduct_positions_directions PairPoly MaybePoly

/--
Positions and directions of `ListPoly ▷ MaybePoly`.
-/
theorem listOfMaybe_positions_directions :
    Nonempty
      (ListOfMaybePoly.A
        ≃ Sigma (fun a : ListPoly.A => ListPoly.B a → MaybePoly.A))
      ∧
    (∀ s : ListOfMaybePoly.A,
      Nonempty
        (ListOfMaybePoly.B s
          ≃ Sigma (fun p : ListPoly.B s.1 => MaybePoly.B (s.2 p)))) := by
  exact compositionProduct_positions_directions ListPoly MaybePoly

/-
==============================================================================
Milestone sanity checks
==============================================================================

These small checks ensure the public composition-product packages are available
from this examples file.
-/

/-- The composition-product core evidence is available. -/
theorem examples_compositionProductEvidenceAvailable :
    CompositionProductEvidence.{0, 0, w} := by
  exact compositionProductEvidence_done

/-- The homogeneous unit/associativity evidence is available. -/
theorem examples_compositionProductMonoidalEvidenceAvailable :
    CompositionProductMonoidalEvidence.{0} := by
  exact compositionProductMonoidalEvidence_done

/-- The full composition-product milestone is available. -/
theorem examples_compositionProductMilestoneAvailable :
    compositionProductMilestone.{0, 0, w} := by
  exact compositionProductMilestone_done

end PolyC.Examples
