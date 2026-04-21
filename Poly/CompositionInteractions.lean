import Poly.CompositionProducts
import Poly.ParallelDistribute

/-
============================================================
Poly Project
File: Poly/CompositionInteractions.lean
============================================================

This file packages the first-pass-plus interaction layer for the composition
product.

Book motivation:
Chapter 6.3 studies categorical properties of the composition product `⊳`.
The first concrete results are the left-distributivity laws:

  (P + Q) ⊳ R ≅ (P ⊳ R) + (Q ⊳ R)
  (P × Q) ⊳ R ≅ (P ⊳ R) × (Q ⊳ R).

In the book, this is Proposition 6.46. It also warns immediately afterward
that the analogous right-distributivity statements do not hold in general.

This file is a first-pass Type-level version of those interaction facts. It
records:

  • positions-and-directions equivalences for left interaction with binary
    coproducts;
  • positions-and-directions equivalences for left interaction with binary
    products;
  • semantic evaluation equivalences for those same interactions;
  • the already-built parallel-product distributivity facts, because Chapter
    6.3 also discusses interaction with parallel products.

This file intentionally does not attempt the full later theory of:

  • left coclosure,
  • preservation of arbitrary limits on the left,
  • connected limits on the right,
  • vertical/cartesian lens interaction.

Those belong to the next book-formalization pass. The present file is the
stable pass-1-plus support layer needed before polynomial comonoids.

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

namespace PolyC

universe u v w

/-
==============================================================================
Left interaction with binary coproducts
==============================================================================

The book's first left-distributivity formula says:

  (P + Q) ⊳ R ≅ (P ⊳ R) + (Q ⊳ R).

At the positions-and-directions level, this is straightforward.

A position of `(P + Q) ⊳ R` is either:
  • a `P`-position together with an `R`-position for each `P`-direction, or
  • a `Q`-position together with an `R`-position for each `Q`-direction.

That is exactly a position of `(P ⊳ R) + (Q ⊳ R)`.
-/

/-- Positions of `(P + Q) ⊳ R` are positions of `(P ⊳ R) + (Q ⊳ R)`. -/
def compositionProduct_sumLeftPositionsEquiv
    (P Q R : PolyC.{u, v}) :
    (compositionProduct (sum P Q) R).A
      ≃
    (sum (compositionProduct P R) (compositionProduct Q R)).A where
  toFun s :=
    match s with
    | ⟨Sum.inl a, k⟩ => Sum.inl ⟨a, k⟩
    | ⟨Sum.inr b, k⟩ => Sum.inr ⟨b, k⟩
  invFun t :=
    match t with
    | Sum.inl ⟨a, k⟩ => ⟨Sum.inl a, k⟩
    | Sum.inr ⟨b, k⟩ => ⟨Sum.inr b, k⟩
  left_inv := by
    intro s
    cases s with
    | mk side k =>
      cases side <;> rfl
  right_inv := by
    intro t
    cases t with
    | inl s =>
      cases s
      rfl
    | inr s =>
      cases s
      rfl

/--
Directions of `(P + Q) ⊳ R` agree with directions of
`(P ⊳ R) + (Q ⊳ R)` at the corresponding position.
-/
def compositionProduct_sumLeftDirectionsEquiv
    (P Q R : PolyC.{u, v})
    (s : (compositionProduct (sum P Q) R).A) :
    (compositionProduct (sum P Q) R).B s
      ≃
    (sum (compositionProduct P R) (compositionProduct Q R)).B
      (compositionProduct_sumLeftPositionsEquiv P Q R s) := by
  cases s with
  | mk side k =>
    cases side with
    | inl a =>
      exact Equiv.refl _
    | inr b =>
      exact Equiv.refl _

/--
Positions-and-directions form of left distributivity of `⊳` over binary
coproducts.
-/
theorem compositionProduct_sumLeft_positions_directions
    (P Q R : PolyC.{u, v}) :
    Nonempty
      ((compositionProduct (sum P Q) R).A
        ≃
       (sum (compositionProduct P R) (compositionProduct Q R)).A)
      ∧
    (∀ s : (compositionProduct (sum P Q) R).A,
      Nonempty
        ((compositionProduct (sum P Q) R).B s
          ≃
         (sum (compositionProduct P R) (compositionProduct Q R)).B
          (compositionProduct_sumLeftPositionsEquiv P Q R s))) := by
  refine ⟨⟨compositionProduct_sumLeftPositionsEquiv P Q R⟩, ?_⟩
  intro s
  exact ⟨compositionProduct_sumLeftDirectionsEquiv P Q R s⟩

/--
Semantic left distributivity of `⊳` over binary coproducts.

This says that evaluation of `(P + Q) ⊳ R` is equivalent to the sum of
evaluations of `P ⊳ R` and `Q ⊳ R`.
-/
def compositionProduct_sumLeftEvalEquiv
    (P Q R : PolyC.{u, v}) (X : Type w) :
    (compositionProduct (sum P Q) R).eval X
      ≃
    Sum ((compositionProduct P R).eval X)
        ((compositionProduct Q R).eval X) :=
  (compositionProductEvalEquiv (sum P Q) R X).trans
    ((evalSumEquiv P Q (R.eval X)).trans
      (Equiv.sumCongr
        (compositionProductEvalEquiv P R X).symm
        (compositionProductEvalEquiv Q R X).symm))

/--
Semantic left distributivity, phrased as evaluation of the target polynomial.
-/
def compositionProduct_sumLeftTargetEvalEquiv
    (P Q R : PolyC.{u, v}) (X : Type w) :
    (compositionProduct (sum P Q) R).eval X
      ≃
    (sum (compositionProduct P R) (compositionProduct Q R)).eval X :=
  (compositionProduct_sumLeftEvalEquiv P Q R X).trans
    (evalSumEquiv (compositionProduct P R) (compositionProduct Q R) X).symm

/-
==============================================================================
Left interaction with binary products
==============================================================================

The book's second left-distributivity formula says:

  (P × Q) ⊳ R ≅ (P ⊳ R) × (Q ⊳ R).

At the positions-and-directions level, a position of `(P × Q) ⊳ R` is:

  • a pair of positions `(a, b)`;
  • an `R`-position for every direction of `P × Q`.

Since directions of `P × Q` are a sum of `P`-directions and `Q`-directions,
this is the same as:

  • a position of `P ⊳ R`;
  • a position of `Q ⊳ R`.
-/

/-- Positions of `(P × Q) ⊳ R` are positions of `(P ⊳ R) × (Q ⊳ R)`. -/
def compositionProduct_prodLeftPositionsEquiv
    (P Q R : PolyC.{u, v}) :
    (compositionProduct (prod P Q) R).A
      ≃
    (prod (compositionProduct P R) (compositionProduct Q R)).A where
  toFun s :=
    ⟨⟨s.1.1, fun p => s.2 (Sum.inl p)⟩,
     ⟨s.1.2, fun q => s.2 (Sum.inr q)⟩⟩
  invFun t :=
    ⟨⟨t.1.1, t.2.1⟩,
      fun slot =>
        match slot with
        | Sum.inl p => t.1.2 p
        | Sum.inr q => t.2.2 q⟩
  left_inv := by
    intro s
    cases s with
    | mk ab k =>
      cases ab with
      | mk a b =>
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext slot
          cases slot <;> rfl
  right_inv := by
    intro t
    cases t with
    | mk left right =>
      cases left with
      | mk a kP =>
        cases right with
        | mk b kQ =>
          apply Prod.ext
          · apply Sigma.ext
            · rfl
            · apply heq_of_eq
              funext p
              rfl
          · apply Sigma.ext
            · rfl
            · apply heq_of_eq
              funext q
              rfl

/--
Directions of `(P × Q) ⊳ R` agree with directions of
`(P ⊳ R) × (Q ⊳ R)` at the corresponding position.
-/
def compositionProduct_prodLeftDirectionsEquiv
    (P Q R : PolyC.{u, v})
    (s : (compositionProduct (prod P Q) R).A) :
    (compositionProduct (prod P Q) R).B s
      ≃
    (prod (compositionProduct P R) (compositionProduct Q R)).B
      (compositionProduct_prodLeftPositionsEquiv P Q R s) := by
  cases s with
  | mk ab k =>
    cases ab with
    | mk a b =>
      refine
        { toFun := ?toFun
          invFun := ?invFun
          left_inv := ?leftInv
          right_inv := ?rightInv }
      · intro d
        cases d with
        | mk slot rdir =>
          cases slot with
          | inl p => exact Sum.inl ⟨p, rdir⟩
          | inr q => exact Sum.inr ⟨q, rdir⟩
      · intro d
        cases d with
        | inl pr => exact ⟨Sum.inl pr.1, pr.2⟩
        | inr qr => exact ⟨Sum.inr qr.1, qr.2⟩
      · intro d
        cases d with
        | mk slot rdir =>
          cases slot <;> rfl
      · intro d
        cases d with
        | inl pr =>
          cases pr
          rfl
        | inr qr =>
          cases qr
          rfl

/--
Positions-and-directions form of left distributivity of `⊳` over binary
products.
-/
theorem compositionProduct_prodLeft_positions_directions
    (P Q R : PolyC.{u, v}) :
    Nonempty
      ((compositionProduct (prod P Q) R).A
        ≃
       (prod (compositionProduct P R) (compositionProduct Q R)).A)
      ∧
    (∀ s : (compositionProduct (prod P Q) R).A,
      Nonempty
        ((compositionProduct (prod P Q) R).B s
          ≃
         (prod (compositionProduct P R) (compositionProduct Q R)).B
          (compositionProduct_prodLeftPositionsEquiv P Q R s))) := by
  refine ⟨⟨compositionProduct_prodLeftPositionsEquiv P Q R⟩, ?_⟩
  intro s
  exact ⟨compositionProduct_prodLeftDirectionsEquiv P Q R s⟩

/--
Semantic left distributivity of `⊳` over binary products.

This says that evaluation of `(P × Q) ⊳ R` is equivalent to the product of
evaluations of `P ⊳ R` and `Q ⊳ R`.
-/
def compositionProduct_prodLeftEvalEquiv
    (P Q R : PolyC.{u, v}) (X : Type w) :
    (compositionProduct (prod P Q) R).eval X
      ≃
    ((compositionProduct P R).eval X
      ×
     (compositionProduct Q R).eval X) :=
  (compositionProductEvalEquiv (prod P Q) R X).trans
    ((evalProdEquiv P Q (R.eval X)).trans
      (Equiv.prodCongr
        (compositionProductEvalEquiv P R X).symm
        (compositionProductEvalEquiv Q R X).symm))

/--
Semantic left distributivity, phrased as evaluation of the target polynomial.
-/
def compositionProduct_prodLeftTargetEvalEquiv
    (P Q R : PolyC.{u, v}) (X : Type w) :
    (compositionProduct (prod P Q) R).eval X
      ≃
    (prod (compositionProduct P R) (compositionProduct Q R)).eval X :=
  (compositionProduct_prodLeftEvalEquiv P Q R X).trans
    (evalProdEquiv (compositionProduct P R) (compositionProduct Q R) X).symm

/-
==============================================================================
Right-distributivity warning
==============================================================================

The book explicitly warns that the analogous right-distributivity statements
do not hold in general:

  P ⊳ (Q × R) ≄ (P ⊳ Q) × (P ⊳ R)
  P ⊳ (Q + R) ≄ (P ⊳ Q) + (P ⊳ R).

So this file deliberately does not assert such theorems.
-/

/-- Documentation marker: right distributivity of `⊳` is not asserted here. -/
def compositionProductRightDistributivityNotAsserted : Prop := True

/-- The right-distributivity warning marker is established. -/
theorem compositionProductRightDistributivityNotAsserted_done :
    compositionProductRightDistributivityNotAsserted := by
  trivial

/-
==============================================================================
Parallel-product interaction already available
==============================================================================

Chapter 6.3 also discusses interaction with parallel products. The concrete
parallel-product distributivity facts were already built in
`Poly/ParallelDistribute.lean`.

We collect them here so the composition-product interaction layer points to
the already-developed parallel side of the project.
-/

/-- Existing left distributivity of parallel product over coproduct. -/
def compositionInteractions_tensorSumLeftIso
    (P Q R : PolyC.{u, v}) :
    ((sum P Q) ⊗ R) ≅ sum (P ⊗ R) (Q ⊗ R) :=
  tensorSumLeftIso P Q R

/-- Existing right distributivity of parallel product over coproduct. -/
def compositionInteractions_tensorSumRightIso
    (P Q R : PolyC.{u, v}) :
    (P ⊗ sum Q R) ≅ sum (P ⊗ Q) (P ⊗ R) :=
  tensorSumRightIso P Q R

/-
==============================================================================
Interaction evidence package
==============================================================================

This package records the first-pass-plus interaction layer that is now
available:

  • left interaction of composition product with binary coproducts;
  • left interaction of composition product with binary products;
  • semantic versions of those two interaction facts;
  • already-built distributivity facts for the parallel product.
-/

/-- Project-local evidence for the Chapter 6.3 interaction layer. -/
structure CompositionInteractionEvidence : Prop where
  compositionLeftCoproduct_positionsDirections :
    ∀ P Q R : PolyC.{u, v},
      Nonempty
        ((compositionProduct (sum P Q) R).A
          ≃
         (sum (compositionProduct P R) (compositionProduct Q R)).A)
        ∧
      (∀ s : (compositionProduct (sum P Q) R).A,
        Nonempty
          ((compositionProduct (sum P Q) R).B s
            ≃
           (sum (compositionProduct P R) (compositionProduct Q R)).B
            (compositionProduct_sumLeftPositionsEquiv P Q R s)))
  compositionLeftProduct_positionsDirections :
    ∀ P Q R : PolyC.{u, v},
      Nonempty
        ((compositionProduct (prod P Q) R).A
          ≃
         (prod (compositionProduct P R) (compositionProduct Q R)).A)
        ∧
      (∀ s : (compositionProduct (prod P Q) R).A,
        Nonempty
          ((compositionProduct (prod P Q) R).B s
            ≃
           (prod (compositionProduct P R) (compositionProduct Q R)).B
            (compositionProduct_prodLeftPositionsEquiv P Q R s)))
  compositionLeftCoproduct_eval :
    ∀ (P Q R : PolyC.{u, v}) (X : Type w),
      Nonempty
        ((compositionProduct (sum P Q) R).eval X
          ≃
         (sum (compositionProduct P R) (compositionProduct Q R)).eval X)
  compositionLeftProduct_eval :
    ∀ (P Q R : PolyC.{u, v}) (X : Type w),
      Nonempty
        ((compositionProduct (prod P Q) R).eval X
          ≃
         (prod (compositionProduct P R) (compositionProduct Q R)).eval X)
  parallelCoproductDistributivity :
    ∀ P Q R : PolyC.{u, v},
      Nonempty (((sum P Q) ⊗ R) ≅ sum (P ⊗ R) (Q ⊗ R))
        ∧
      Nonempty ((P ⊗ sum Q R) ≅ sum (P ⊗ Q) (P ⊗ R))

/-- The Chapter 6.3 first-pass-plus interaction evidence is established. -/
theorem compositionInteractionEvidence_done :
    CompositionInteractionEvidence.{u, v, w} := by
  refine ⟨?sumPD, ?prodPD, ?sumEval, ?prodEval, ?tensorDist⟩
  · intro P Q R
    exact compositionProduct_sumLeft_positions_directions P Q R
  · intro P Q R
    exact compositionProduct_prodLeft_positions_directions P Q R
  · intro P Q R X
    exact ⟨compositionProduct_sumLeftTargetEvalEquiv P Q R X⟩
  · intro P Q R X
    exact ⟨compositionProduct_prodLeftTargetEvalEquiv P Q R X⟩
  · intro P Q R
    exact
      ⟨⟨compositionInteractions_tensorSumLeftIso P Q R⟩,
       ⟨compositionInteractions_tensorSumRightIso P Q R⟩⟩

/-- Documentation-only marker for the Chapter 6.3 interaction layer. -/
def compositionInteractionsMilestone : Prop :=
  CompositionInteractionEvidence.{u, v, w}

/-- The composition-interactions milestone is established. -/
theorem compositionInteractionsMilestone_done :
    compositionInteractionsMilestone.{u, v, w} := by
  exact compositionInteractionEvidence_done

end PolyC
