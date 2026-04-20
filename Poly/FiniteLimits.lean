import Poly.Universal
import Poly.Equalizers
import Poly.SemanticEqualizers
import Poly.Pullbacks
import Poly.SemanticPullbacks
import Poly.IndexedProducts
import Poly.IndexedCoproducts
import Poly.PullbackPositionsDirections

/-
============================================================
EE598 — Poly Project
File: Poly/FiniteLimits.lean
============================================================

This file packages the finite-limit layer developed so far for the
category `PolyC` of polynomial functors / containers.

The point of this file is not to construct new objects. Instead, it
collects the project-local universal-property results that have already
been proved in earlier files:

  • binary products, from `Poly/Universal.lean`,
  • indexed products, from `Poly/IndexedProducts.lean`,
  • equalizers, from `Poly/Equalizers.lean`,
  • pointwise semantic equalizers, from `Poly/SemanticEqualizers.lean`,
  • pullbacks, from `Poly/Pullbacks.lean`,
  • pointwise semantic pullbacks, from `Poly/SemanticPullbacks.lean`,
  • pullback positions/directions, from
    `Poly/PullbackPositionsDirections.lean`.

This file also imports indexed coproducts from
`Poly/IndexedCoproducts.lean`. Indexed coproducts are not finite limits,
but they are part of the same first-pass positions-and-directions layer:
for indexed products of polynomials, the position type is an indexed
product, while the direction type is an indexed coproduct.

Mathematical background:
Chapter 5 of *Polynomial Functors* explains that products and equalizers
are enough to build limits, and more generally that limits in `Poly` are
computed by taking limits on positions and colimits on directions. In this
development, we keep the constructions explicit: we compute the relevant
polynomial objects and prove their universal properties directly in the
positions-and-directions presentation.

Relationship to Mathlib:
Mathlib already contains the general abstract category-theory API for
products, equalizers, pullbacks, limits, and finite limits. This file is not
intended to replace that API. Its purpose is to collect the concrete,
book-guided constructions in `PolyC` before a later bridge to Mathlib's
`Limits` API.

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

`Universal.lean` proves the binary product universal property by giving an
explicit equivalence

  Hom(R, prod P Q) ≃ Hom(R, P) × Hom(R, Q).

The definitions below simply re-expose that result from the finite-limits
namespace layer.
-/

/-- Binary product object, collected as part of the finite-limit interface. -/
def finiteProduct (P Q : PolyC.{u, v}) : PolyC.{u, v} :=
  prod P Q

/-- First projection from the collected binary product. -/
def finiteProductFst (P Q : PolyC.{u, v}) : finiteProduct P Q ⟶ P :=
  prodFst P Q

/-- Second projection from the collected binary product. -/
def finiteProductSnd (P Q : PolyC.{u, v}) : finiteProduct P Q ⟶ Q :=
  prodSnd P Q

/-- Product universal property, restated as an equivalence of hom-types. -/
def finiteProductHomEquiv (R P Q : PolyC.{u, v}) :
    (R ⟶ finiteProduct P Q) ≃ (R ⟶ P) × (R ⟶ Q) :=
  homProdEquiv R P Q

/-- The product lift has the expected first projection. -/
theorem finiteProductLift_fst
    {R P Q : PolyC.{u, v}}
    (f : R ⟶ P) (g : R ⟶ Q) :
    prodLift (R := R) (P := P) (Q := Q) f g ≫ finiteProductFst P Q = f := by
  exact prodLift_fst (R := R) (P := P) (Q := Q) f g

/-- The product lift has the expected second projection. -/
theorem finiteProductLift_snd
    {R P Q : PolyC.{u, v}}
    (f : R ⟶ P) (g : R ⟶ Q) :
    prodLift (R := R) (P := P) (Q := Q) f g ≫ finiteProductSnd P Q = g := by
  exact prodLift_snd (R := R) (P := P) (Q := Q) f g

/-
==============================================================================
Indexed products
==============================================================================

`IndexedProducts.lean` gives the small-indexed product construction in the
positions-and-directions presentation:

  positions:
    ∀ i, (F i).A

  directions:
    Σ i, (F i).B (a i)

This is the explicit indexed-product ingredient needed for the first-pass
small-limits story.
-/

/-- Indexed product object, collected as part of the limit interface. -/
def finiteIndexedProduct {I : Type v}
    (F : I → PolyC.{max u v, v}) : PolyC.{max u v, v} :=
  indexedProd F

/-- Projection from the collected indexed product to the `i`th factor. -/
def finiteIndexedProductProj {I : Type v}
    (F : I → PolyC.{max u v, v}) (i : I) :
    finiteIndexedProduct F ⟶ F i :=
  indexedProdProj F i

/-- Universal lift into the collected indexed product. -/
def finiteIndexedProductLift {I : Type v}
    (F : I → PolyC.{max u v, v})
    {R : PolyC.{max u v, v}}
    (h : ∀ i : I, R ⟶ F i) :
    R ⟶ finiteIndexedProduct F :=
  indexedProdLift F h

/-- Indexed product universal property, restated as an equivalence of hom-types. -/
def finiteIndexedProductHomEquiv {I : Type v}
    (R : PolyC.{max u v, v})
    (F : I → PolyC.{max u v, v}) :
    (R ⟶ finiteIndexedProduct F) ≃ (∀ i : I, R ⟶ F i) :=
  homIndexedProdEquiv R F

/-- The indexed-product lift has the expected `i`th projection. -/
theorem finiteIndexedProductLift_proj {I : Type v}
    (F : I → PolyC.{max u v, v})
    {R : PolyC.{max u v, v}}
    (h : ∀ i : I, R ⟶ F i) (i : I) :
    finiteIndexedProductLift F h ≫ finiteIndexedProductProj F i = h i := by
  exact indexedProdLift_proj F h i

/-- The explicit indexed product satisfies its project-local universal property. -/
theorem finiteIndexedProduct_isIndexedProduct {I : Type v}
    (F : I → PolyC.{max u v, v}) :
    IsIndexedProduct F (finiteIndexedProduct F) (finiteIndexedProductProj F) := by
  exact indexedProd_isIndexedProduct F

/--
Positions of the collected indexed product are indexed products of positions.
-/
def finiteIndexedProductPositionsEquiv {I : Type v}
    (F : I → PolyC.{max u v, v}) :
    (finiteIndexedProduct F).A ≃ (∀ i : I, (F i).A) :=
  indexedProdPositionsEquiv F

/--
Directions of the collected indexed product are indexed coproducts of the
corresponding direction types.
-/
def finiteIndexedProductDirectionsEquiv {I : Type v}
    (F : I → PolyC.{max u v, v})
    (a : (finiteIndexedProduct F).A) :
    (finiteIndexedProduct F).B a ≃ Sigma (fun i : I => (F i).B (a i)) :=
  indexedProdDirectionsEquiv F a

/--
Evaluation of an indexed product is the indexed product of evaluations.
-/
def finiteIndexedProductEvalEquiv {I : Type v}
    (F : I → PolyC.{max u v, v}) (X : Type w) :
    (finiteIndexedProduct F).eval X ≃ (∀ i : I, (F i).eval X) :=
  evalIndexedProdEquiv F X

/-
==============================================================================
Indexed coproducts as supporting direction-side colimit data
==============================================================================

Indexed coproducts are not finite limits. They are included here only because
the book's positions-and-directions limit formula uses colimits of direction
types, and indexed products of polynomials already use indexed coproducts on
directions.
-/

/-- Indexed coproduct object, collected as supporting positions/directions data. -/
def finiteLimitsIndexedCoproduct {I : Type u}
    (F : I → PolyC.{u, v}) : PolyC.{u, v} :=
  indexedCoprod F

/-- Injection of the `i`th factor into the collected indexed coproduct. -/
def finiteLimitsIndexedCoproductIn {I : Type u}
    (F : I → PolyC.{u, v}) (i : I) :
    F i ⟶ finiteLimitsIndexedCoproduct F :=
  indexedCoprodIn F i

/-- Universal map out of the collected indexed coproduct. -/
def finiteLimitsIndexedCoproductDesc {I : Type u}
    (F : I → PolyC.{u, v})
    {R : PolyC.{u, v}}
    (h : ∀ i : I, F i ⟶ R) :
    finiteLimitsIndexedCoproduct F ⟶ R :=
  indexedCoprodDesc F h

/-- Indexed coproduct universal property, restated as an equivalence of hom-types. -/
def finiteLimitsIndexedCoproductHomEquiv {I : Type u}
    (F : I → PolyC.{u, v})
    (R : PolyC.{u, v}) :
    (finiteLimitsIndexedCoproduct F ⟶ R) ≃ (∀ i : I, F i ⟶ R) :=
  homIndexedCoprodEquiv F R

/-- The explicit indexed coproduct satisfies its project-local universal property. -/
theorem finiteLimitsIndexedCoproduct_isIndexedCoproduct {I : Type u}
    (F : I → PolyC.{u, v}) :
    IsIndexedCoproduct
      F
      (finiteLimitsIndexedCoproduct F)
      (finiteLimitsIndexedCoproductIn F) := by
  exact indexedCoprod_isIndexedCoproduct F

/-- Positions of an indexed coproduct are indexed coproducts of positions. -/
def finiteLimitsIndexedCoproductPositionsEquiv {I : Type u}
    (F : I → PolyC.{u, v}) :
    (finiteLimitsIndexedCoproduct F).A ≃ Sigma (fun i : I => (F i).A) :=
  indexedCoprodPositionsEquiv F

/-- Directions of an indexed coproduct are inherited from the selected factor. -/
def finiteLimitsIndexedCoproductDirectionsEquiv {I : Type u}
    (F : I → PolyC.{u, v})
    (ia : (finiteLimitsIndexedCoproduct F).A) :
    (finiteLimitsIndexedCoproduct F).B ia ≃ (F ia.1).B ia.2 :=
  indexedCoprodDirectionsEquiv F ia

/-- Evaluation of an indexed coproduct is the indexed coproduct of evaluations. -/
def finiteLimitsIndexedCoproductEvalEquiv {I : Type u}
    (F : I → PolyC.{u, v}) (X : Type w) :
    (finiteLimitsIndexedCoproduct F).eval X ≃ Sigma (fun i : I => (F i).eval X) :=
  evalIndexedCoprodEquiv F X

/-
==============================================================================
Equalizers
==============================================================================

`Equalizers.lean` constructs the equalizer of parallel maps `f g : P ⟶ Q`.
The positions are positions of `P` on which the two forward maps agree, and
the directions are a quotient implementing the corresponding coequalizer of
directions.
-/

/-- Equalizer object, collected as part of the finite-limit interface. -/
def finiteEqualizer {P Q : PolyC.{u, v}} (f g : P ⟶ Q) : PolyC.{u, v} :=
  EqObj (f := f) (g := g)

/-- Canonical equalizer map into the source object. -/
def finiteEqualizerMap {P Q : PolyC.{u, v}} (f g : P ⟶ Q) :
    finiteEqualizer f g ⟶ P :=
  eq (f := f) (g := g)

/-- The collected equalizer map equalizes the two parallel arrows. -/
theorem finiteEqualizer_condition {P Q : PolyC.{u, v}} (f g : P ⟶ Q) :
    finiteEqualizerMap f g ≫ f = finiteEqualizerMap f g ≫ g := by
  exact eq_comp_eq (f := f) (g := g)

/-- The collected equalizer satisfies the project-local equalizer universal property. -/
theorem finiteEqualizer_isEqualizer {P Q : PolyC.{u, v}} (f g : P ⟶ Q) :
    IsEqualizer f g (finiteEqualizerMap f g) := by
  exact eqObj_isEqualizer (f := f) (g := g)

/-
==============================================================================
Semantic equalizers
==============================================================================

`SemanticEqualizers.lean` proves the pointwise version of the equalizer
construction: after evaluating at any type `X`, the equalizer object gives
the function-level equalizer of the induced semantic maps.
-/

/-- The evaluated equalizer is a function-level equalizer at each type `X`. -/
theorem finiteEqualizer_semantic {P Q : PolyC.{u, v}}
    (f g : P ⟶ Q) (X : Type v) :
    IsFunctionEqualizer
      (PolyC.map f (X := X) : P.eval X → Q.eval X)
      (PolyC.map g (X := X) : P.eval X → Q.eval X)
      (PolyC.map (finiteEqualizerMap f g) (X := X) :
        (finiteEqualizer f g).eval X → P.eval X) := by
  exact eval_eq_isEqualizer (f := f) (g := g) X

/-
==============================================================================
Pullbacks
==============================================================================

`Pullbacks.lean` constructs pullbacks from products and equalizers:

  PullObj f g = EqObj (pullLeft f g) (pullRight f g).

This is the standard categorical construction of a pullback as an equalizer
of two maps out of a product.
-/

/-- Pullback object, collected as part of the finite-limit interface. -/
def finitePullback {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S) :
    PolyC.{u, v} :=
  PullObj f g

/-- First projection from the collected pullback. -/
def finitePullbackFst {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S) :
    finitePullback f g ⟶ P :=
  pullFst f g

/-- Second projection from the collected pullback. -/
def finitePullbackSnd {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S) :
    finitePullback f g ⟶ Q :=
  pullSnd f g

/-- The collected pullback square commutes. -/
theorem finitePullback_condition {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S) :
    finitePullbackFst f g ≫ f = finitePullbackSnd f g ≫ g := by
  exact pullback_condition f g

/-- The collected pullback satisfies the project-local pullback universal property. -/
theorem finitePullback_isPullback {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S) :
    IsPullback f g (finitePullbackFst f g) (finitePullbackSnd f g) := by
  exact pullObj_isPullback f g

/-- The universal lift into the collected pullback. -/
def finitePullbackLift {R P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    R ⟶ finitePullback f g :=
  pullLift f g a b h

/-- The finite-pullback lift has the requested first projection. -/
theorem finitePullbackLift_fst {R P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    finitePullbackLift f g a b h ≫ finitePullbackFst f g = a := by
  exact pullLift_fst f g a b h

/-- The finite-pullback lift has the requested second projection. -/
theorem finitePullbackLift_snd {R P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    finitePullbackLift f g a b h ≫ finitePullbackSnd f g = b := by
  exact pullLift_snd f g a b h

/-- The two projection equations for the finite-pullback lift, packaged together. -/
theorem finitePullbackLift_factors {R P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    finitePullbackLift f g a b h ≫ finitePullbackFst f g = a
      ∧
    finitePullbackLift f g a b h ≫ finitePullbackSnd f g = b := by
  exact pullLift_factors f g a b h

/-
==============================================================================
Pullback positions and directions
==============================================================================

`PullbackPositionsDirections.lean` identifies the derived pullback object with
the book's direct description:

  • positions are pairs of positions over the base;
  • directions are the pushout quotient of the two direction maps.
-/

/-- Positions of the collected pullback are pairs of positions over the base. -/
def finitePullbackPositionsEquiv {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S) :
    (finitePullback f g).A ≃ PullShape f g :=
  pullObjPositionsEquiv f g

/--
Directions of the collected pullback are the pushout quotient of the two
direction maps.
-/
def finitePullbackDirectionsEquiv {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : PullShape f g) :
    (finitePullback f g).B ((finitePullbackPositionsEquiv f g).symm a)
      ≃ PullDirPushout f g a :=
  pullObjDirectionsEquiv f g a

/-- The first projection on pullback positions is the first component. -/
theorem finitePullbackFst_onShapes_direct {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : PullShape f g) :
    (finitePullbackFst f g).onShapes ((finitePullbackPositionsEquiv f g).symm a)
      =
    a.1.1 := by
  simpa [finitePullbackFst, finitePullbackPositionsEquiv]
    using pullFst_onShapes_direct f g a

/-- The second projection on pullback positions is the second component. -/
theorem finitePullbackSnd_onShapes_direct {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : PullShape f g) :
    (finitePullbackSnd f g).onShapes ((finitePullbackPositionsEquiv f g).symm a)
      =
    a.1.2 := by
  simpa [finitePullbackSnd, finitePullbackPositionsEquiv]
    using pullSnd_onShapes_direct f g a

/-- The first projection pulls directions by the left pushout inclusion. -/
theorem finitePullbackFst_onPos_direct {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : PullShape f g)
    (d : P.B a.1.1) :
    finitePullbackDirectionsEquiv f g a
      ((finitePullbackFst f g).onPos ((finitePullbackPositionsEquiv f g).symm a) d)
      =
    pullDirInl f g a d := by
  simpa [finitePullbackFst, finitePullbackDirectionsEquiv, finitePullbackPositionsEquiv]
    using pullFst_onPos_direct f g a d

/-- The second projection pulls directions by the right pushout inclusion. -/
theorem finitePullbackSnd_onPos_direct {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : PullShape f g)
    (d : Q.B a.1.2) :
    finitePullbackDirectionsEquiv f g a
      ((finitePullbackSnd f g).onPos ((finitePullbackPositionsEquiv f g).symm a) d)
      =
    pullDirInr f g a d := by
  simpa [finitePullbackSnd, finitePullbackDirectionsEquiv, finitePullbackPositionsEquiv]
    using pullSnd_onPos_direct f g a d

/--
The collected pullback has the direct positions-and-directions description from
the book.
-/
theorem finitePullback_positions_directions {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S) :
    Nonempty
      ((finitePullback f g).A ≃ PullShape f g)
      ∧
    (∀ a : PullShape f g,
      Nonempty
        ((finitePullback f g).B ((finitePullbackPositionsEquiv f g).symm a)
          ≃ PullDirPushout f g a)) := by
  refine ⟨⟨finitePullbackPositionsEquiv f g⟩, ?_⟩
  intro a
  exact ⟨finitePullbackDirectionsEquiv f g a⟩

/-
==============================================================================
Semantic pullbacks
==============================================================================

`SemanticPullbacks.lean` proves that the explicit pullback object evaluates
pointwise as a pullback square of ordinary functions.
-/

/-- The evaluated pullback is a function-level pullback at each type `X`. -/
theorem finitePullback_semantic {P Q S : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S) (X : Type v) :
    IsFunctionPullback
      (PolyC.map f (X := X) : P.eval X → S.eval X)
      (PolyC.map g (X := X) : Q.eval X → S.eval X)
      (PolyC.map (finitePullbackFst f g) (X := X) :
        (finitePullback f g).eval X → P.eval X)
      (PolyC.map (finitePullbackSnd f g) (X := X) :
        (finitePullback f g).eval X → Q.eval X) := by
  exact eval_pullback_isPullback (f := f) (g := g) X

/-
==============================================================================
Milestone summary
==============================================================================

The declarations above give a compact public surface for the finite-limit
fragment and small-product ingredients that have been explicitly constructed
so far.

This file intentionally does not assert Mathlib `HasFiniteLimits` or
`HasLimits`. The next layer is to connect these concrete constructions to
Mathlib's abstract `CategoryTheory.Limits` API.
-/

/-- A documentation-only marker for the explicit finite-limit layer in `PolyC`. -/
def finiteLimitsMilestone : Prop := True

/-- The finite-limit milestone is established by the collected constructions above. -/
theorem finiteLimitsMilestone_done : finiteLimitsMilestone := by
  trivial

end PolyC
