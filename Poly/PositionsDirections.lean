import Poly.SmallLimits

/-
============================================================
Poly Project
File: Poly/PositionsDirections.lean
============================================================

This file collects the first-pass positions-and-directions theorem family for
`PolyC`.

Book motivation:
Chapter 5 explains that limits in `Poly` are computed by taking limits on
positions and colimits on directions. In the book's slogan:

  • positions of a limit are limits of positions;
  • directions of a limit are colimits of directions.

The fully abstract Mathlib-facing theorem belongs to a later pass. In this
first-pass Type-level development, we collect the concrete cases already
constructed in the project:

  • binary products,
  • indexed products,
  • equalizers,
  • pullbacks,
  • indexed coproducts as the basic colimit-side companion.

The point of this file is not to build new objects. It is a readable public
surface for the computations already proved in:

  • `Poly.Universal`,
  • `Poly.IndexedProducts`,
  • `Poly.IndexedCoproducts`,
  • `Poly.Equalizers`,
  • `Poly.Pullbacks`,
  • `Poly.PullbackPositionsDirections`,
  • `Poly.FiniteLimits`,
  • `Poly.SmallLimits`.

Terminology note:
the codebase still uses the internal field names

  • `A`        = positions,
  • `B a`      = directions at position `a`,
  • `onShapes` = forward map on positions,
  • `onPos`    = backward pullback map on directions.

Human-facing mathematical descriptions should use positions and directions.
============================================================
-/

open CategoryTheory

namespace PolyC

universe u v w

/-
==============================================================================
Binary products
==============================================================================

For binary products, positions are pairs of positions and directions are a sum
of directions.
-/

/-- Positions of a binary product are pairs of positions. -/
def positionsDirections_binaryProduct_positions
    (P Q : PolyC.{u, v}) :
    (finiteProduct P Q).A ≃ P.A × Q.A :=
  Equiv.refl _

/-- Directions of a binary product are a sum of directions. -/
def positionsDirections_binaryProduct_directions
    (P Q : PolyC.{u, v})
    (a : (finiteProduct P Q).A) :
    (finiteProduct P Q).B a ≃ Sum (P.B a.1) (Q.B a.2) :=
  Equiv.refl _

/-- Binary products satisfy the positions-and-directions product formula. -/
theorem positionsDirections_binaryProduct
    (P Q : PolyC.{u, v}) :
    Nonempty ((finiteProduct P Q).A ≃ P.A × Q.A)
      ∧
    (∀ a : (finiteProduct P Q).A,
      Nonempty ((finiteProduct P Q).B a ≃ Sum (P.B a.1) (Q.B a.2))) := by
  refine ⟨⟨positionsDirections_binaryProduct_positions P Q⟩, ?_⟩
  intro a
  exact ⟨positionsDirections_binaryProduct_directions P Q a⟩

/-
==============================================================================
Indexed products
==============================================================================

For indexed products, positions are dependent products and directions are
dependent sums. This is the product case of the book's limit formula.
-/

/-- Positions of an indexed product are indexed products of positions. -/
def positionsDirections_indexedProduct_positions {I : Type v}
    (F : I → PolyC.{max u v, v}) :
    (finiteIndexedProduct F).A ≃ (∀ i : I, (F i).A) :=
  finiteIndexedProductPositionsEquiv F

/-- Directions of an indexed product are indexed coproducts of directions. -/
def positionsDirections_indexedProduct_directions {I : Type v}
    (F : I → PolyC.{max u v, v})
    (a : (finiteIndexedProduct F).A) :
    (finiteIndexedProduct F).B a ≃ Sigma (fun i : I => (F i).B (a i)) :=
  finiteIndexedProductDirectionsEquiv F a

/-- Indexed products satisfy the positions-and-directions product formula. -/
theorem positionsDirections_indexedProduct {I : Type v}
    (F : I → PolyC.{max u v, v}) :
    Nonempty ((finiteIndexedProduct F).A ≃ ∀ i : I, (F i).A)
      ∧
    (∀ a : (finiteIndexedProduct F).A,
      Nonempty
        ((finiteIndexedProduct F).B a
          ≃ Sigma (fun i : I => (F i).B (a i)))) := by
  exact smallLimit_indexedProduct_positions_directions F

/-- Evaluation of an indexed product is the indexed product of evaluations. -/
def positionsDirections_indexedProduct_eval {I : Type v}
    (F : I → PolyC.{max u v, v}) (X : Type w) :
    (finiteIndexedProduct F).eval X ≃ (∀ i : I, (F i).eval X) :=
  finiteIndexedProductEvalEquiv F X

/-
==============================================================================
Equalizers
==============================================================================

For equalizers, positions are equalized positions and directions are the
coequalizer quotient of directions.
-/

/-- Positions of an equalizer are positions on which the two position maps agree. -/
def positionsDirections_equalizer_positions
    {P Q : PolyC.{u, v}} (f g : P ⟶ Q) :
    (finiteEqualizer f g).A ≃ EqA (f := f) (g := g) :=
  Equiv.refl _

/-- Directions of an equalizer are the quotient/coequalizer direction type. -/
def positionsDirections_equalizer_directions
    {P Q : PolyC.{u, v}} (f g : P ⟶ Q)
    (a : (finiteEqualizer f g).A) :
    (finiteEqualizer f g).B a ≃ EqB (f := f) (g := g) a :=
  Equiv.refl _

/-- Equalizers satisfy the positions-and-directions equalizer formula. -/
theorem positionsDirections_equalizer
    {P Q : PolyC.{u, v}} (f g : P ⟶ Q) :
    Nonempty ((finiteEqualizer f g).A ≃ EqA (f := f) (g := g))
      ∧
    (∀ a : (finiteEqualizer f g).A,
      Nonempty
        ((finiteEqualizer f g).B a
          ≃ EqB (f := f) (g := g) a)) := by
  exact smallLimit_equalizer_positions_directions f g

/-- Evaluation of an equalizer is a function-level equalizer. -/
theorem positionsDirections_equalizer_eval
    {P Q : PolyC.{u, v}} (f g : P ⟶ Q) (X : Type v) :
    IsFunctionEqualizer
      (PolyC.map f (X := X) : P.eval X → Q.eval X)
      (PolyC.map g (X := X) : P.eval X → Q.eval X)
      (PolyC.map (finiteEqualizerMap f g) (X := X) :
        (finiteEqualizer f g).eval X → P.eval X) := by
  exact finiteEqualizer_semantic f g X

/-
==============================================================================
Pullbacks
==============================================================================

The pullback object is constructed from products and equalizers. The direct
positions-and-directions theorem identifies it with the book's explicit
pullback computation:

  • positions are pairs over the base;
  • directions are the pushout quotient of the two direction maps.
-/

/-- Positions of a pullback are pairs of positions over the base. -/
def positionsDirections_pullback_positions
    {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S) :
    (finitePullback f g).A ≃ PullShape f g :=
  finitePullbackPositionsEquiv f g

/-- Directions of a pullback are the pushout quotient of directions. -/
def positionsDirections_pullback_directions
    {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S)
    (a : PullShape f g) :
    (finitePullback f g).B ((positionsDirections_pullback_positions f g).symm a)
      ≃ PullDirPushout f g a :=
  finitePullbackDirectionsEquiv f g a

/-- Pullbacks satisfy the positions-and-directions pullback formula. -/
theorem positionsDirections_pullback
    {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S) :
    Nonempty ((finitePullback f g).A ≃ PullShape f g)
      ∧
    (∀ a : PullShape f g,
      Nonempty
        ((finitePullback f g).B ((positionsDirections_pullback_positions f g).symm a)
          ≃ PullDirPushout f g a)) := by
  refine ⟨⟨positionsDirections_pullback_positions f g⟩, ?_⟩
  intro a
  exact ⟨positionsDirections_pullback_directions f g a⟩

/-- Evaluation of a pullback is a function-level pullback. -/
theorem positionsDirections_pullback_eval
    {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S) (X : Type v) :
    IsFunctionPullback
      (PolyC.map f (X := X) : P.eval X → S.eval X)
      (PolyC.map g (X := X) : Q.eval X → S.eval X)
      (PolyC.map (finitePullbackFst f g) (X := X) :
        (finitePullback f g).eval X → P.eval X)
      (PolyC.map (finitePullbackSnd f g) (X := X) :
        (finitePullback f g).eval X → Q.eval X) := by
  exact finitePullback_semantic f g X

/-
==============================================================================
Indexed coproducts
==============================================================================

Indexed coproducts are included here as the basic colimit-side construction.
For coproducts, positions are dependent sums and directions are inherited from
the selected summand.
-/

/-- Positions of an indexed coproduct are indexed coproducts of positions. -/
def positionsDirections_indexedCoproduct_positions {I : Type u}
    (F : I → PolyC.{u, v}) :
    (finiteLimitsIndexedCoproduct F).A ≃ Sigma (fun i : I => (F i).A) :=
  finiteLimitsIndexedCoproductPositionsEquiv F

/-- Directions of an indexed coproduct are inherited from the selected summand. -/
def positionsDirections_indexedCoproduct_directions {I : Type u}
    (F : I → PolyC.{u, v})
    (ia : (finiteLimitsIndexedCoproduct F).A) :
    (finiteLimitsIndexedCoproduct F).B ia ≃ (F ia.1).B ia.2 :=
  finiteLimitsIndexedCoproductDirectionsEquiv F ia

/-- Indexed coproducts satisfy the positions-and-directions coproduct formula. -/
theorem positionsDirections_indexedCoproduct {I : Type u}
    (F : I → PolyC.{u, v}) :
    Nonempty ((finiteLimitsIndexedCoproduct F).A ≃ Sigma (fun i : I => (F i).A))
      ∧
    (∀ ia : (finiteLimitsIndexedCoproduct F).A,
      Nonempty ((finiteLimitsIndexedCoproduct F).B ia ≃ (F ia.1).B ia.2)) := by
  refine ⟨⟨positionsDirections_indexedCoproduct_positions F⟩, ?_⟩
  intro ia
  exact ⟨positionsDirections_indexedCoproduct_directions F ia⟩

/-- Evaluation of an indexed coproduct is the indexed coproduct of evaluations. -/
def positionsDirections_indexedCoproduct_eval {I : Type u}
    (F : I → PolyC.{u, v}) (X : Type w) :
    (finiteLimitsIndexedCoproduct F).eval X ≃ Sigma (fun i : I => (F i).eval X) :=
  finiteLimitsIndexedCoproductEvalEquiv F X

/-
==============================================================================
Main first-pass theorem family
==============================================================================

This structure is a project-local package of the positions-and-directions
formulas already built in the first pass. It is not yet the fully abstract
Mathlib theorem about all limits and colimits. That bridge belongs to the
Mathlib-facing pass.
-/

/-- The collected first-pass positions-and-directions theorem family. -/
structure PositionsDirectionsEvidence : Prop where
  binaryProducts :
    ∀ P Q : PolyC.{u, v},
      Nonempty ((finiteProduct P Q).A ≃ P.A × Q.A)
        ∧
      (∀ a : (finiteProduct P Q).A,
        Nonempty ((finiteProduct P Q).B a ≃ Sum (P.B a.1) (Q.B a.2)))
  indexedProducts :
    ∀ {I : Type v} (F : I → PolyC.{max u v, v}),
      Nonempty ((finiteIndexedProduct F).A ≃ ∀ i : I, (F i).A)
        ∧
      (∀ a : (finiteIndexedProduct F).A,
        Nonempty
          ((finiteIndexedProduct F).B a
            ≃ Sigma (fun i : I => (F i).B (a i))))
  equalizers :
    ∀ {P Q : PolyC.{u, v}} (f g : P ⟶ Q),
      Nonempty ((finiteEqualizer f g).A ≃ EqA (f := f) (g := g))
        ∧
      (∀ a : (finiteEqualizer f g).A,
        Nonempty
          ((finiteEqualizer f g).B a
            ≃ EqB (f := f) (g := g) a))
  pullbacks :
    ∀ {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S),
      Nonempty ((finitePullback f g).A ≃ PullShape f g)
        ∧
      (∀ a : PullShape f g,
        Nonempty
          ((finitePullback f g).B ((positionsDirections_pullback_positions f g).symm a)
            ≃ PullDirPushout f g a))
  indexedCoproducts :
    ∀ {I : Type u} (F : I → PolyC.{u, v}),
      Nonempty ((finiteLimitsIndexedCoproduct F).A ≃ Sigma (fun i : I => (F i).A))
        ∧
      (∀ ia : (finiteLimitsIndexedCoproduct F).A,
        Nonempty ((finiteLimitsIndexedCoproduct F).B ia ≃ (F ia.1).B ia.2))

/-- The first-pass positions-and-directions theorem family is established. -/
theorem positionsDirectionsEvidence_done : PositionsDirectionsEvidence.{u, v} := by
  refine ⟨?binaryProducts, ?indexedProducts, ?equalizers, ?pullbacks, ?indexedCoproducts⟩
  · intro P Q
    exact positionsDirections_binaryProduct P Q
  · intro I F
    exact positionsDirections_indexedProduct F
  · intro P Q f g
    exact positionsDirections_equalizer f g
  · intro P Q S f g
    exact positionsDirections_pullback f g
  · intro I F
    exact positionsDirections_indexedCoproduct F

/-- A documentation-only marker for the positions-and-directions milestone. -/
def positionsDirectionsMilestone : Prop := PositionsDirectionsEvidence.{u, v}

/-- The positions-and-directions milestone is established by the theorem family. -/
theorem positionsDirectionsMilestone_done : positionsDirectionsMilestone.{u, v} := by
  exact positionsDirectionsEvidence_done

end PolyC
