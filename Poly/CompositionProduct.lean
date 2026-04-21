import Poly.CompOnMorphisms
import Poly.CompSemantics
import Poly.CompMonoidal

/-
============================================================
Poly Project
File: Poly/CompositionProduct.lean
============================================================

This file packages the Chapter 6 composition product layer for `PolyC`.

The construction itself is already present in earlier files:

  • `Poly/Composition.lean`
      object-level composition/substitution of polynomial functors;

  • `Poly/CompOnMorphisms.lean`
      composition on morphisms and the bifunctorial action;

  • `Poly/CompSemantics.lean`
      semantic substitution, saying evaluation sends composition product
      to ordinary functor composition up to natural isomorphism;

  • `Poly/CompMonodial.lean`
      unitors and associator for the composition product.

The purpose of this file is not to rebuild those constructions. It gives a
clean book-facing public surface for the composition product:

  • positions and directions of `P ▷ Q`;
  • semantic substitution `(P ▷ Q)(X) ≃ P(Q(X))`;
  • morphism-level action;
  • functoriality of the morphism-level action;
  • unit and associativity isomorphisms in the homogeneous universe case.

Mathematical background:
Chapter 6 of *Polynomial Functors* studies the composition product, a
monoidal structure on `Poly` given by substituting one polynomial into
another. This structure is essential for the later theory of polynomial
comonoids.

Universe note:
For general `P Q : PolyC.{u,v}`, object-level composition lands in

  PolyC.{max u v, v}.

Thus the fully closed monoidal structure is easiest to state in the
homogeneous case `PolyC.{u,u}`. The general object-level and morphism-level
composition product is still exposed below.

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
Object-level composition product
==============================================================================

For polynomial functors `P` and `Q`, the composition product `P ▷ Q` is the
polynomial obtained by substituting `Q` into `P`.

Positions:
  choose an outer position `a : P.A`, and then for every direction
  `p : P.B a`, choose an inner position of `Q`.

Directions:
  choose an outer direction `p : P.B a`, and then a direction of `Q`
  at the chosen inner position.
-/

/-- Book-facing alias for the object-level composition product. -/
def compositionProduct (P Q : PolyC.{u, v}) : PolyC.{max u v, v} :=
  composeObj P Q

/--
Positions of the composition product.

A position of `P ▷ Q` is an outer position of `P` together with, for each
outer direction, a position of `Q`.
-/
def compositionProductPositionsEquiv (P Q : PolyC.{u, v}) :
    (compositionProduct P Q).A
      ≃
    Sigma (fun a : P.A => P.B a → Q.A) :=
  Equiv.refl _

/--
Directions of the composition product.

At a composite position `(a, k)`, a direction consists of an outer direction
`p : P.B a` and an inner direction of `Q` at the selected position `k p`.
-/
def compositionProductDirectionsEquiv
    (P Q : PolyC.{u, v})
    (s : (compositionProduct P Q).A) :
    (compositionProduct P Q).B s
      ≃
    Sigma (fun p : P.B s.1 => Q.B (s.2 p)) :=
  Equiv.refl _

/--
The composition product has the expected positions-and-directions formula.
-/
theorem compositionProduct_positions_directions
    (P Q : PolyC.{u, v}) :
    Nonempty
      ((compositionProduct P Q).A
        ≃ Sigma (fun a : P.A => P.B a → Q.A))
      ∧
    (∀ s : (compositionProduct P Q).A,
      Nonempty
        ((compositionProduct P Q).B s
          ≃ Sigma (fun p : P.B s.1 => Q.B (s.2 p)))) := by
  refine ⟨⟨compositionProductPositionsEquiv P Q⟩, ?_⟩
  intro s
  exact ⟨compositionProductDirectionsEquiv P Q s⟩

/-
==============================================================================
Semantic substitution
==============================================================================

Evaluation sends the composition product to ordinary substitution of functors:

  (P ▷ Q)(X) ≃ P(Q(X)).
-/

/--
Semantic substitution equivalence for the composition product.
-/
def compositionProductEvalEquiv
    (P Q : PolyC.{u, v}) (X : Type w) :
    (compositionProduct P Q).eval X ≃ P.eval (Q.eval X) :=
  evalComposeEquiv P Q X

/--
Natural-isomorphism version of semantic substitution.

This says that the evaluation functor of `P ▷ Q` is naturally isomorphic to
first evaluating `Q` and then evaluating `P`.
-/
def compositionProductEvalIso
    (P Q : PolyC.{u, v}) :
    (compositionProduct P Q).evalFunctor ≅
      (Q.evalFunctor ⋙ P.evalFunctor) :=
  evalComposeIso P Q

/-
==============================================================================
Morphism-level composition product
==============================================================================

The composition product acts on lenses/morphisms.

Given

  f : P ⟶ P'
  g : Q ⟶ Q'

we get

  f ▷ g : P ▷ Q ⟶ P' ▷ Q'.
-/

/-- Book-facing alias for composition on morphisms. -/
def compositionProductMap
    {P P' Q Q' : PolyC.{u, v}}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    compositionProduct P Q ⟶ compositionProduct P' Q' :=
  composeHom f g

/--
The composition product map preserves identities.
-/
theorem compositionProductMap_id
    (P Q : PolyC.{u, v}) :
    compositionProductMap (𝟙 P) (𝟙 Q)
      =
    𝟙 (compositionProduct P Q) := by
  apply Hom.ext
  · funext s
    cases s with
    | mk a k =>
      rfl
  · intro s
    apply heq_of_eq
    funext d
    cases s with
    | mk a k =>
      cases d with
      | mk p q =>
        rfl

/--
The composition product map preserves composition.
-/
theorem compositionProductMap_comp
    {P₀ P₁ P₂ Q₀ Q₁ Q₂ : PolyC.{u, v}}
    (f₁ : P₀ ⟶ P₁) (f₂ : P₁ ⟶ P₂)
    (g₁ : Q₀ ⟶ Q₁) (g₂ : Q₁ ⟶ Q₂) :
    compositionProductMap (f₁ ≫ f₂) (g₁ ≫ g₂)
      =
    compositionProductMap f₁ g₁ ≫ compositionProductMap f₂ g₂ := by
  apply Hom.ext
  · funext s
    cases s with
    | mk a k =>
      rfl
  · intro s
    apply heq_of_eq
    funext d
    cases s with
    | mk a k =>
      cases d with
      | mk p q =>
        rfl

/--
The bifunctorial form of the composition product.

This is the already-built bifunctor from `CompOnMorphisms.lean`, re-exposed
through the composition-product interface.
-/
def compositionProductBifunctor :
    (PolyC.{u, v} × PolyC.{u, v}) ⥤ PolyC.{max u v, v} :=
  compBifunctor

/-
==============================================================================
Unit and associativity isomorphisms
==============================================================================

In the homogeneous universe case, the composition product is closed on
`PolyC.{u,u}`. The unit object is the variable polynomial `y`.

The earlier file `CompMonodial.lean` constructs the left unitor, right unitor,
and associator. We expose them here under composition-product names.
-/

/-- The unit polynomial for the composition product. -/
def compositionProductUnit : PolyC.{u, u} :=
  PolyC.y.{u, u}

/-- Left unitor for the composition product: `y ▷ P ≅ P`. -/
def compositionProductLeftUnitor
    (P : PolyC.{u, u}) :
    composeObj (PolyC.y.{u, u}) P ≅ P :=
  compLeftUnitor P

/-- Right unitor for the composition product: `P ▷ y ≅ P`. -/
def compositionProductRightUnitor
    (P : PolyC.{u, u}) :
    composeObj P (PolyC.y.{u, u}) ≅ P :=
  compRightUnitor P

/-- Associator for the composition product. -/
def compositionProductAssociator
    (P Q R : PolyC.{u, u}) :
    composeObj (composeObj P Q) R ≅ composeObj P (composeObj Q R) :=
  compAssociator P Q R

/-
==============================================================================
Project-local evidence packages
==============================================================================

These packages are not Mathlib `MonoidalCategory` instances. They record the
concrete ingredients that have been built and packaged in this first-pass-plus
composition-product layer.

A later Mathlib-facing file can use these ingredients to attempt a genuine
`MonoidalCategory` instance on the homogeneous universe version of `PolyC`.
-/

/--
Evidence that the object-level and morphism-level composition product core is
available.
-/
structure CompositionProductEvidence : Prop where
  positionsDirections :
    ∀ P Q : PolyC.{u, v},
      Nonempty
        ((compositionProduct P Q).A
          ≃ Sigma (fun a : P.A => P.B a → Q.A))
        ∧
      (∀ s : (compositionProduct P Q).A,
        Nonempty
          ((compositionProduct P Q).B s
            ≃ Sigma (fun p : P.B s.1 => Q.B (s.2 p))))
  semanticSubstitution :
    ∀ (P Q : PolyC.{u, v}) (X : Type w),
      Nonempty ((compositionProduct P Q).eval X ≃ P.eval (Q.eval X))
  mapIdentities :
    ∀ P Q : PolyC.{u, v},
      compositionProductMap (𝟙 P) (𝟙 Q)
        =
      𝟙 (compositionProduct P Q)
  mapComposition :
    ∀ {P₀ P₁ P₂ Q₀ Q₁ Q₂ : PolyC.{u, v}}
      (f₁ : P₀ ⟶ P₁) (f₂ : P₁ ⟶ P₂)
      (g₁ : Q₀ ⟶ Q₁) (g₂ : Q₁ ⟶ Q₂),
      compositionProductMap (f₁ ≫ f₂) (g₁ ≫ g₂)
        =
      compositionProductMap f₁ g₁ ≫ compositionProductMap f₂ g₂

/-- The composition-product core evidence is established. -/
theorem compositionProductEvidence_done :
    CompositionProductEvidence.{u, v, w} := by
  refine ⟨?pd, ?sem, ?ids, ?comp⟩
  · intro P Q
    exact compositionProduct_positions_directions P Q
  · intro P Q X
    exact ⟨compositionProductEvalEquiv P Q X⟩
  · intro P Q
    exact compositionProductMap_id P Q
  · intro P₀ P₁ P₂ Q₀ Q₁ Q₂ f₁ f₂ g₁ g₂
    exact compositionProductMap_comp f₁ f₂ g₁ g₂

/--
Evidence that the homogeneous composition product has unitors and associator.

This is the project-local monoidal-structure ingredient, not yet a Mathlib
`MonoidalCategory` instance.
-/
structure CompositionProductMonoidalEvidence : Prop where
  hasLeftUnitor :
    ∀ P : PolyC.{u, u},
      Nonempty (composeObj (PolyC.y.{u, u}) P ≅ P)
  hasRightUnitor :
    ∀ P : PolyC.{u, u},
      Nonempty (composeObj P (PolyC.y.{u, u}) ≅ P)
  hasAssociator :
    ∀ P Q R : PolyC.{u, u},
      Nonempty (composeObj (composeObj P Q) R ≅ composeObj P (composeObj Q R))

/-- The homogeneous unit and associativity evidence is established. -/
theorem compositionProductMonoidalEvidence_done :
    CompositionProductMonoidalEvidence.{u} := by
  refine ⟨?left, ?right, ?assoc⟩
  · intro P
    exact ⟨compositionProductLeftUnitor P⟩
  · intro P
    exact ⟨compositionProductRightUnitor P⟩
  · intro P Q R
    exact ⟨compositionProductAssociator P Q R⟩

/-- Documentation-only marker for the Chapter 6 composition-product core. -/
def compositionProductMilestone : Prop :=
  CompositionProductEvidence.{u, v, w} ∧ CompositionProductMonoidalEvidence.{u}

/-- The composition-product milestone is established. -/
theorem compositionProductMilestone_done :
    compositionProductMilestone.{u, v, w} := by
  exact ⟨compositionProductEvidence_done, compositionProductMonoidalEvidence_done⟩

end PolyC
