import Poly.FiniteLimits

/-
============================================================
EE598 — Poly Project
File: Poly/SmallLimits.lean
============================================================

This file packages the first-pass small-limits layer for the category
`PolyC` of polynomial functors / containers.

The point of this file is not to prove Mathlib's abstract theorem

  HasLimits PolyC.

That bridge belongs to the later Mathlib-facing pass. Instead, this file
records the concrete ingredients from the book-guided construction:

  • indexed products, from `Poly/IndexedProducts.lean`;
  • equalizers, from `Poly/Equalizers.lean`;
  • semantic indexed products, from `Poly/IndexedProducts.lean`;
  • semantic equalizers, from `Poly/SemanticEqualizers.lean`;
  • pullbacks as a derived finite-limit construction;
  • pullback positions and directions.

Mathematical background:
Chapter 5 of *Polynomial Functors* proves that `Poly` has all small limits
by using the standard category-theoretic fact that products and equalizers
are enough to construct small limits. The same section summarizes the
positions-and-directions computation of limits by the slogan:

  • positions of a limit are limits of positions;
  • directions of a limit are colimits of directions.

In this Type-level development, we keep this first pass explicit and local:
we package the indexed-product and equalizer constructions that implement
that theorem, without yet invoking Mathlib's `CategoryTheory.Limits` API.

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
Small-limit ingredients
==============================================================================

The book-level theorem says that products and equalizers generate small
limits. In this project-local first pass, we record precisely those concrete
ingredients: indexed products and equalizers.
-/

/--
Project-local package of the explicit ingredients used to build small limits
in `PolyC`: indexed products and equalizers.

This is intentionally not a Mathlib `HasLimits` instance. It is a concrete
book-guided milestone that can later be related to Mathlib's limits API.
-/
structure SmallLimitIngredients : Prop where
  hasIndexedProducts :
    ∀ {I : Type v} (F : I → PolyC.{max u v, v}),
      IsIndexedProduct F (finiteIndexedProduct F) (finiteIndexedProductProj F)
  hasEqualizers :
    ∀ {P Q : PolyC.{max u v, v}} (f g : P ⟶ Q),
      IsEqualizer f g (finiteEqualizerMap f g)

/--
The explicit indexed products and equalizers constructed in earlier files give
the project-local small-limit ingredients.
-/
theorem smallLimitIngredients_done : SmallLimitIngredients.{u, v} := by
  refine ⟨?products, ?equalizers⟩
  · intro I F
    exact finiteIndexedProduct_isIndexedProduct F
  · intro P Q f g
    exact finiteEqualizer_isEqualizer f g

/-
==============================================================================
Semantic small-limit ingredients
==============================================================================

For the constructions already built, evaluation behaves as expected:
indexed products evaluate to indexed products of evaluations, and equalizers
evaluate to function-level equalizers.
-/

/--
Project-local package of the semantic facts supporting the small-limits layer.
-/
structure SemanticSmallLimitIngredients : Prop where
  indexedProductsPointwise :
    ∀ {I : Type v} (F : I → PolyC.{max u v, v}) (X : Type w),
      Nonempty ((finiteIndexedProduct F).eval X ≃ ∀ i : I, (F i).eval X)
  equalizersPointwise :
    ∀ {P Q : PolyC.{max u v, v}} (f g : P ⟶ Q) (X : Type v),
      IsFunctionEqualizer
        (PolyC.map f (X := X) : P.eval X → Q.eval X)
        (PolyC.map g (X := X) : P.eval X → Q.eval X)
        (PolyC.map (finiteEqualizerMap f g) (X := X) :
          (finiteEqualizer f g).eval X → P.eval X)

/--
The semantic indexed-product and semantic equalizer theorems supply the
pointwise semantics for the project-local small-limit ingredients.
-/
theorem semanticSmallLimitIngredients_done :
    SemanticSmallLimitIngredients.{u, v, w} := by
  refine ⟨?products, ?equalizers⟩
  · intro I F X
    exact ⟨finiteIndexedProductEvalEquiv F X⟩
  · intro P Q f g X
    exact finiteEqualizer_semantic f g X

/-
==============================================================================
Indexed products: positions and directions
==============================================================================

For an indexed product, positions are indexed products of positions and
directions are indexed coproducts of the corresponding direction types.
This is the product case of the book's positions/directions limit slogan.
-/

/--
The indexed product has positions given by the indexed product of positions
and directions given by the indexed coproduct of directions.
-/
theorem smallLimit_indexedProduct_positions_directions {I : Type v}
    (F : I → PolyC.{max u v, v}) :
    Nonempty ((finiteIndexedProduct F).A ≃ ∀ i : I, (F i).A)
      ∧
    (∀ a : (finiteIndexedProduct F).A,
      Nonempty
        ((finiteIndexedProduct F).B a
          ≃ Sigma (fun i : I => (F i).B (a i)))) := by
  refine ⟨⟨finiteIndexedProductPositionsEquiv F⟩, ?_⟩
  intro a
  exact ⟨finiteIndexedProductDirectionsEquiv F a⟩

/--
Evaluation of the indexed product is the indexed product of evaluations.
-/
def smallLimit_indexedProduct_eval_equiv {I : Type v}
    (F : I → PolyC.{max u v, v}) (X : Type w) :
    (finiteIndexedProduct F).eval X ≃ ∀ i : I, (F i).eval X :=
  finiteIndexedProductEvalEquiv F X

/--
The indexed product satisfies its project-local universal property.
-/
theorem smallLimit_indexedProduct_universal {I : Type v}
    (F : I → PolyC.{max u v, v}) :
    IsIndexedProduct F (finiteIndexedProduct F) (finiteIndexedProductProj F) := by
  exact finiteIndexedProduct_isIndexedProduct F

/-
==============================================================================
Equalizers: positions and directions
==============================================================================

For an equalizer, positions are an equalizer of positions and directions are a
coequalizer quotient of directions. The construction is carried out in
`Poly/Equalizers.lean`; here we expose the positions/directions shape as part
of the small-limits package.
-/

/--
The equalizer object has equalizer positions and coequalizer-quotient
directions.
-/
theorem smallLimit_equalizer_positions_directions
    {P Q : PolyC.{u, v}} (f g : P ⟶ Q) :
    Nonempty ((finiteEqualizer f g).A ≃ EqA (f := f) (g := g))
      ∧
    (∀ a : (finiteEqualizer f g).A,
      Nonempty
        ((finiteEqualizer f g).B a
          ≃ EqB (f := f) (g := g) a)) := by
  refine ⟨⟨Equiv.refl _⟩, ?_⟩
  intro a
  exact ⟨Equiv.refl _⟩

/--
The equalizer satisfies its project-local universal property.
-/
theorem smallLimit_equalizer_universal
    {P Q : PolyC.{u, v}} (f g : P ⟶ Q) :
    IsEqualizer f g (finiteEqualizerMap f g) := by
  exact finiteEqualizer_isEqualizer f g

/--
The evaluated equalizer is a function-level equalizer at each type `X`.
-/
theorem smallLimit_equalizer_semantic
    {P Q : PolyC.{u, v}} (f g : P ⟶ Q) (X : Type v) :
    IsFunctionEqualizer
      (PolyC.map f (X := X) : P.eval X → Q.eval X)
      (PolyC.map g (X := X) : P.eval X → Q.eval X)
      (PolyC.map (finiteEqualizerMap f g) (X := X) :
        (finiteEqualizer f g).eval X → P.eval X) := by
  exact finiteEqualizer_semantic f g X

/-
==============================================================================
Pullbacks as derived small limits
==============================================================================

Pullbacks are finite limits. In this project they are constructed from binary
products and equalizers, and their semantic behavior is proved pointwise.
-/

/--
The explicit pullback satisfies the project-local pullback universal property.
-/
theorem smallLimit_pullback_universal
    {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S) :
    IsPullback f g (finitePullbackFst f g) (finitePullbackSnd f g) := by
  exact finitePullback_isPullback f g

/--
The explicit pullback square commutes.
-/
theorem smallLimit_pullback_condition
    {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S) :
    finitePullbackFst f g ≫ f = finitePullbackSnd f g ≫ g := by
  exact finitePullback_condition f g

/--
The pullback has positions given by pairs over the base and directions given by
the pushout quotient of directions.
-/
theorem smallLimit_pullback_positions_directions
    {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S) :
    Nonempty ((finitePullback f g).A ≃ PullShape f g)
      ∧
    (∀ a : PullShape f g,
      Nonempty
        ((finitePullback f g).B ((finitePullbackPositionsEquiv f g).symm a)
          ≃ PullDirPushout f g a)) := by
  exact finitePullback_positions_directions f g

/--
The evaluated pullback is a function-level pullback at each type `X`.
-/
theorem smallLimit_pullback_semantic
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
Milestone summary
==============================================================================

This marker records the first-pass small-limits layer:

  indexed products + equalizers,

with pullbacks included as the central finite-limit example derived from
products and equalizers. The formal Mathlib `HasLimits` bridge is intentionally
left for the next pass.
-/

/-- A documentation-only marker for the project-local small-limits layer. -/
def smallLimitsMilestone : Prop := SmallLimitIngredients.{u, v}

/-- The small-limits milestone is established by the collected ingredients. -/
theorem smallLimitsMilestone_done : smallLimitsMilestone.{u, v} := by
  exact smallLimitIngredients_done

end PolyC
