import Poly.PositionsDirections
import Poly.Coequalizers

/-
============================================================
Poly Project
File: Poly/SmallColimits.lean
============================================================

This file packages the first-pass small-colimits layer for the category
`PolyC` of polynomial functors / containers.

The point of this file is not to prove Mathlib's abstract theorem

  HasColimits PolyC.

That bridge belongs to the later Mathlib-facing pass. Instead, this file
records the concrete ingredients from the book-guided construction:

  • indexed coproducts, from `Poly/IndexedCoproducts.lean`;
  • coequalizers, from `Poly/Coequalizers.lean`.

Mathematical background:
Theorem 5.44 of *Polynomial Functors* proves that `Poly` has all small
colimits by using the standard category-theoretic fact that coproducts and
coequalizers are enough to construct small colimits.

In the positions-and-directions presentation, the coequalizer construction
has:

  • positions given by connected components / a quotient of positions;
  • directions given by limits of direction-sets over each connected
    component.

That construction is implemented explicitly in `Poly/Coequalizers.lean`.
This file collects it together with indexed coproducts as the project-local
small-colimits milestone.

Important semantic warning:
Unlike limits, general colimits in `Poly` do not necessarily coincide with
pointwise colimits in the ambient functor category `Set^Set`. Therefore this
file does not assert a pointwise semantic coequalizer theorem. Indexed
coproducts have a pointwise evaluation equivalence, but general coequalizers
are intentionally kept as internal `PolyC` colimits.

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
Indexed coproducts
==============================================================================

For an indexed family of polynomial functors

  F : I → PolyC,

the indexed coproduct has:

  positions:
    Σ i : I, (F i).A

  directions at `(i, a)`:
    (F i).B a.

This is the coproduct-side ingredient in the small-colimits construction.
-/

/-- Indexed coproduct object, collected as part of the small-colimits interface. -/
def smallIndexedCoproduct {I : Type u}
    (F : I → PolyC.{u, max u v}) : PolyC.{u, max u v} :=
  indexedCoprod F

/-- Injection of the `i`th summand into the collected indexed coproduct. -/
def smallIndexedCoproductIn {I : Type u}
    (F : I → PolyC.{u, max u v}) (i : I) :
    F i ⟶ smallIndexedCoproduct F :=
  indexedCoprodIn F i

/-- Universal map out of the collected indexed coproduct. -/
def smallIndexedCoproductDesc {I : Type u}
    (F : I → PolyC.{u, max u v})
    {R : PolyC.{u, max u v}}
    (h : ∀ i : I, F i ⟶ R) :
    smallIndexedCoproduct F ⟶ R :=
  indexedCoprodDesc F h

/-- Indexed coproduct universal property, restated as an equivalence of hom-types. -/
def smallIndexedCoproductHomEquiv {I : Type u}
    (F : I → PolyC.{u, max u v})
    (R : PolyC.{u, max u v}) :
    (smallIndexedCoproduct F ⟶ R) ≃ (∀ i : I, F i ⟶ R) :=
  homIndexedCoprodEquiv F R

/-- The copairing map restricts to the original map on the `i`th summand. -/
theorem smallIndexedCoproductIn_desc {I : Type u}
    (F : I → PolyC.{u, max u v})
    {R : PolyC.{u, max u v}}
    (h : ∀ i : I, F i ⟶ R) (i : I) :
    smallIndexedCoproductIn F i ≫ smallIndexedCoproductDesc F h = h i := by
  exact indexedCoprodIn_desc F h i

/-- The explicit indexed coproduct satisfies its project-local universal property. -/
theorem smallIndexedCoproduct_isIndexedCoproduct {I : Type u}
    (F : I → PolyC.{u, max u v}) :
    IsIndexedCoproduct
      F
      (smallIndexedCoproduct F)
      (smallIndexedCoproductIn F) := by
  exact indexedCoprod_isIndexedCoproduct F

/-- Positions of an indexed coproduct are indexed coproducts of positions. -/
def smallIndexedCoproductPositionsEquiv {I : Type u}
    (F : I → PolyC.{u, max u v}) :
    (smallIndexedCoproduct F).A ≃ Sigma (fun i : I => (F i).A) :=
  indexedCoprodPositionsEquiv F

/-- Directions of an indexed coproduct are inherited from the selected summand. -/
def smallIndexedCoproductDirectionsEquiv {I : Type u}
    (F : I → PolyC.{u, max u v})
    (ia : (smallIndexedCoproduct F).A) :
    (smallIndexedCoproduct F).B ia ≃ (F ia.1).B ia.2 :=
  indexedCoprodDirectionsEquiv F ia

/-- Indexed coproducts satisfy the positions-and-directions coproduct formula. -/
theorem smallIndexedCoproduct_positions_directions {I : Type u}
    (F : I → PolyC.{u, max u v}) :
    Nonempty ((smallIndexedCoproduct F).A ≃ Sigma (fun i : I => (F i).A))
      ∧
    (∀ ia : (smallIndexedCoproduct F).A,
      Nonempty ((smallIndexedCoproduct F).B ia ≃ (F ia.1).B ia.2)) := by
  refine ⟨⟨smallIndexedCoproductPositionsEquiv F⟩, ?_⟩
  intro ia
  exact ⟨smallIndexedCoproductDirectionsEquiv F ia⟩

/-- Evaluation of an indexed coproduct is the indexed coproduct of evaluations. -/
def smallIndexedCoproductEvalEquiv {I : Type u}
    (F : I → PolyC.{u, max u v}) (X : Type w) :
    (smallIndexedCoproduct F).eval X ≃ Sigma (fun i : I => (F i).eval X) :=
  evalIndexedCoprodEquiv F X

/-
==============================================================================
Coequalizers
==============================================================================

`Coequalizers.lean` constructs coequalizers internally in `PolyC`.

Given parallel maps

  f g : P ⟶ Q,

the coequalizer object has:

  positions:
    quotient components of `Q.A` generated by
      f.onShapes p ~ g.onShapes p;

  directions:
    compatible families over each quotient component.

This is the concrete Type-level version of the book's construction by
connected components on positions and limits on directions.
-/

/-- Coequalizer object, collected as part of the small-colimits interface. -/
def smallCoequalizer {P Q : PolyC.{u, max u v}} (f g : P ⟶ Q) :
    PolyC.{u, max u v} :=
  CoeqObj f g

/-- Canonical coequalizer map. -/
def smallCoequalizerMap {P Q : PolyC.{u, max u v}} (f g : P ⟶ Q) :
    Q ⟶ smallCoequalizer f g :=
  coeq f g

/-- The collected coequalizer map coequalizes the two parallel arrows. -/
theorem smallCoequalizer_condition {P Q : PolyC.{u, max u v}}
    (f g : P ⟶ Q) :
    f ≫ smallCoequalizerMap f g = g ≫ smallCoequalizerMap f g := by
  exact coeq_comp_eq f g

/-- The collected coequalizer satisfies the project-local coequalizer property. -/
theorem smallCoequalizer_isCoequalizer {P Q : PolyC.{u, max u v}}
    (f g : P ⟶ Q) :
    IsCoequalizer f g (smallCoequalizerMap f g) := by
  exact coeqObj_isCoequalizer f g

/-- Universal map out of the collected coequalizer. -/
def smallCoequalizerDesc
    {P Q R : PolyC.{u, max u v}}
    (f g : P ⟶ Q)
    (h : Q ⟶ R)
    (heq : f ≫ h = g ≫ h) :
    smallCoequalizer f g ⟶ R :=
  coeqDesc f g h heq

/-- The universal map factors the original coequalizing arrow. -/
theorem smallCoequalizerDesc_fac
    {P Q R : PolyC.{u, max u v}}
    (f g : P ⟶ Q)
    (h : Q ⟶ R)
    (heq : f ≫ h = g ≫ h) :
    smallCoequalizerMap f g ≫ smallCoequalizerDesc f g h heq = h := by
  exact coeqDesc_fac f g h heq

/-- Uniqueness of the universal map out of the collected coequalizer. -/
theorem smallCoequalizerDesc_unique
    {P Q R : PolyC.{u, max u v}}
    (f g : P ⟶ Q)
    (h : Q ⟶ R)
    (heq : f ≫ h = g ≫ h)
    (u : smallCoequalizer f g ⟶ R)
    (hu : smallCoequalizerMap f g ≫ u = h) :
    u = smallCoequalizerDesc f g h heq := by
  exact coeqDesc_unique f g h heq u hu

/-- Coequalizer positions are quotient components of positions. -/
def smallCoequalizerPositionsEquiv {P Q : PolyC.{u, max u v}}
    (f g : P ⟶ Q) :
    (smallCoequalizer f g).A ≃ CoeqA f g :=
  coeqPositionsEquiv f g

/-- Coequalizer directions are compatible families over each position component. -/
def smallCoequalizerDirectionsEquiv {P Q : PolyC.{u, max u v}}
    (f g : P ⟶ Q)
    (c : (smallCoequalizer f g).A) :
    (smallCoequalizer f g).B c ≃ CoeqB f g c :=
  coeqDirectionsEquiv f g c

/-- The collected coequalizer has the book's positions-and-directions shape. -/
theorem smallCoequalizer_positions_directions {P Q : PolyC.{u, max u v}}
    (f g : P ⟶ Q) :
    Nonempty ((smallCoequalizer f g).A ≃ CoeqA f g)
      ∧
    (∀ c : (smallCoequalizer f g).A,
      Nonempty ((smallCoequalizer f g).B c ≃ CoeqB f g c)) := by
  exact coeq_positions_directions f g

/-
==============================================================================
Small-colimit ingredients
==============================================================================

The book-level theorem says that coproducts and coequalizers generate small
colimits. In this first pass, we record the concrete ingredients without yet
invoking Mathlib's `CategoryTheory.Limits` API.
-/

/--
Project-local package of the explicit ingredients used to build small colimits
in `PolyC`: indexed coproducts and coequalizers.
-/
structure SmallColimitIngredients : Prop where
  hasIndexedCoproducts :
    ∀ {I : Type u} (F : I → PolyC.{u, max u v}),
      IsIndexedCoproduct F (smallIndexedCoproduct F) (smallIndexedCoproductIn F)
  hasCoequalizers :
    ∀ {P Q : PolyC.{u, max u v}} (f g : P ⟶ Q),
      IsCoequalizer f g (smallCoequalizerMap f g)

/--
The explicit indexed coproducts and coequalizers constructed in earlier files
give the project-local small-colimit ingredients.
-/
theorem smallColimitIngredients_done : SmallColimitIngredients.{u, v} := by
  refine ⟨?coproducts, ?coequalizers⟩
  · intro I F
    exact smallIndexedCoproduct_isIndexedCoproduct F
  · intro P Q f g
    exact smallCoequalizer_isCoequalizer f g

/-
==============================================================================
Positions-and-directions colimit evidence
==============================================================================

For the colimit constructions currently packaged here:

  • indexed coproducts have positions given by dependent sums and directions
    inherited from the selected summand;
  • coequalizers have positions given by quotient components and directions
    given by compatible families, i.e. limits over those components.
-/

/-- The collected positions-and-directions evidence for the small-colimits layer. -/
structure SmallColimitPositionsDirectionsEvidence : Prop where
  indexedCoproducts :
    ∀ {I : Type u} (F : I → PolyC.{u, max u v}),
      Nonempty ((smallIndexedCoproduct F).A ≃ Sigma (fun i : I => (F i).A))
        ∧
      (∀ ia : (smallIndexedCoproduct F).A,
        Nonempty ((smallIndexedCoproduct F).B ia ≃ (F ia.1).B ia.2))
  coequalizers :
    ∀ {P Q : PolyC.{u, max u v}} (f g : P ⟶ Q),
      Nonempty ((smallCoequalizer f g).A ≃ CoeqA f g)
        ∧
      (∀ c : (smallCoequalizer f g).A,
        Nonempty ((smallCoequalizer f g).B c ≃ CoeqB f g c))

/-- The small-colimit positions-and-directions evidence is established. -/
theorem smallColimitPositionsDirectionsEvidence_done :
    SmallColimitPositionsDirectionsEvidence.{u, v} := by
  refine ⟨?coproducts, ?coequalizers⟩
  · intro I F
    exact smallIndexedCoproduct_positions_directions F
  · intro P Q f g
    exact smallCoequalizer_positions_directions f g

/-
==============================================================================
Semantic warning and indexed-coproduct semantics
==============================================================================

Indexed coproducts evaluate pointwise as indexed coproducts of evaluations.
General coequalizers are deliberately not given a semantic pointwise
coequalizer theorem here, because general colimits in `Poly` do not coincide
with pointwise colimits in `Set^Set`.
-/

/--
Project-local semantic fact for the coproduct side of the small-colimits layer.

There is intentionally no corresponding general semantic coequalizer field.
-/
structure SemanticSmallColimitCoproductFacts : Prop where
  indexedCoproductsPointwise :
    ∀ {I : Type u} (F : I → PolyC.{u, max u v}) (X : Type w),
      Nonempty ((smallIndexedCoproduct F).eval X ≃ Sigma (fun i : I => (F i).eval X))

/-- Indexed coproducts have the expected pointwise semantic behavior. -/
theorem semanticSmallColimitCoproductFacts_done :
    SemanticSmallColimitCoproductFacts.{u, v, w} := by
  refine ⟨?_⟩
  intro I F X
  exact ⟨smallIndexedCoproductEvalEquiv F X⟩

/-
==============================================================================
Milestone summary
==============================================================================

This marker records the first-pass small-colimits layer:

  indexed coproducts + coequalizers.

The formal Mathlib `HasColimits` bridge is intentionally left for the next
pass.
-/

/-- A documentation-only marker for the project-local small-colimits layer. -/
def smallColimitsMilestone : Prop := SmallColimitIngredients.{u, v}

/-- The small-colimits milestone is established by the collected ingredients. -/
theorem smallColimitsMilestone_done : smallColimitsMilestone.{u, v} := by
  exact smallColimitIngredients_done

end PolyC
