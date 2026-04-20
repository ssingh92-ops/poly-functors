import Poly.Core

/-
============================================================
EE598 — Poly Project
File: Poly/IndexedProducts.lean
============================================================

This file constructs indexed products in the category `PolyC` of polynomial
functors / containers.

Book motivation:
Chapter 5 explains that limits in `Poly` are computed by taking limits on
positions and colimits on directions. For products, this says:

  • positions of the product are products of positions;
  • directions at a product-position are coproducts of the corresponding
    direction types.

For an indexed family of polynomials

  F : I → PolyC,

the product object therefore has:

  positions:
    a dependent function choosing a position in every `F i`,

      Π i : I, (F i).A,

  directions at such a position `a`:
    a dependent sum choosing an index and then a direction at that index,

      Σ i : I, (F i).B (a i).

This is the indexed version of the binary product already implemented in
`Poly/Universal.lean`, where binary product positions are pairs and binary
product directions are a sum.

Universe note:
The index type `I` contributes to the direction type

  Σ i : I, (F i).B (a i).

So, in this Type-level implementation, the index universe must be no larger
than the directions universe of the product. We state the construction for

  I : Type v
  F : I → PolyC.{max u v, v}

so that:

  • the position type `Π i, (F i).A` lives in `Type (max u v)`;
  • the direction type `Σ i, (F i).B (a i)` lives in `Type v`;
  • the product object remains in `PolyC.{max u v, v}`.

This is the Lean-native version of the book's small-indexed product formula
inside the current homogeneous universe presentation of `PolyC`.

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
Indexed product object
==============================================================================
-/

/--
The indexed product of a family of polynomial functors.

A position is a choice of a position in every factor. A direction at such a
position is a choice of an index together with a direction in that factor.
-/
def indexedProd {I : Type v} (F : I → PolyC.{max u v, v}) :
    PolyC.{max u v, v} where
  A := ∀ i : I, (F i).A
  B := fun a => Sigma (fun i : I => (F i).B (a i))

/--
The positions of an indexed product are the indexed product of the positions.
This is definitional, but the explicit equivalence is useful as a named API.
-/
def indexedProdPositionsEquiv {I : Type v} (F : I → PolyC.{max u v, v}) :
    (indexedProd F).A ≃ (∀ i : I, (F i).A) :=
  Equiv.refl _

/--
The directions of an indexed product are the indexed coproduct of the
corresponding direction types. This is the indexed-product instance of the
book's "limit positions, colimit directions" mnemonic.
-/
def indexedProdDirectionsEquiv {I : Type v}
    (F : I → PolyC.{max u v, v})
    (a : (indexedProd F).A) :
    (indexedProd F).B a ≃ Sigma (fun i : I => (F i).B (a i)) :=
  Equiv.refl _

/-
==============================================================================
Product projections
==============================================================================
-/

/--
Projection from the indexed product to the `i`th factor.
-/
def indexedProdProj {I : Type v}
    (F : I → PolyC.{max u v, v}) (i : I) :
    indexedProd F ⟶ F i where
  onShapes := fun a => a i
  onPos := fun _ d => ⟨i, d⟩

/-
==============================================================================
Universal lift into an indexed product
==============================================================================
-/

/--
Given a cone over the family `F`, build the induced map into the indexed
product.
-/
def indexedProdLift {I : Type v}
    (F : I → PolyC.{max u v, v})
    {R : PolyC.{max u v, v}}
    (h : ∀ i : I, R ⟶ F i) :
    R ⟶ indexedProd F where
  onShapes := fun r i => (h i).onShapes r
  onPos := fun r d => (h d.1).onPos r d.2

/--
The universal lift followed by the `i`th projection is the original `i`th map.
-/
theorem indexedProdLift_proj {I : Type v}
    (F : I → PolyC.{max u v, v})
    {R : PolyC.{max u v, v}}
    (h : ∀ i : I, R ⟶ F i) (i : I) :
    indexedProdLift F h ≫ indexedProdProj F i = h i := by
  apply Hom.ext
  · funext r
    rfl
  · intro r
    apply heq_of_eq
    funext d
    rfl

/-
==============================================================================
Universal property as an equivalence of hom-types
==============================================================================
-/

/--
Universal property of the indexed product, packaged as an explicit equivalence:

  Hom(R, Πᵢ F i) ≃ Πᵢ Hom(R, F i).
-/
def homIndexedProdEquiv {I : Type v}
    (R : PolyC.{max u v, v})
    (F : I → PolyC.{max u v, v}) :
    (R ⟶ indexedProd F) ≃ (∀ i : I, R ⟶ F i) where
  toFun h := fun i => h ≫ indexedProdProj F i
  invFun h := indexedProdLift F h
  left_inv := by
    intro h
    -- Work directly with the concrete morphism structure.
    change PolyC.Hom R (indexedProd F) at h
    cases h with
    | mk hShapes hPos =>
        apply Hom.ext
        · funext r
          funext i
          rfl
        · intro r
          apply heq_of_eq
          funext d
          cases d with
          | mk i dir => rfl
  right_inv := by
    intro h
    funext i
    exact indexedProdLift_proj F h i

/--
Eta rule for maps into an indexed product.
-/
theorem indexedProd_eta {I : Type v}
    (F : I → PolyC.{max u v, v})
    {R : PolyC.{max u v, v}}
    (h : R ⟶ indexedProd F) :
    indexedProdLift F (fun i => h ≫ indexedProdProj F i) = h := by
  exact (homIndexedProdEquiv R F).left_inv h

/--
Uniqueness for maps into an indexed product.
-/
theorem indexedProdLift_unique {I : Type v}
    (F : I → PolyC.{max u v, v})
    {R : PolyC.{max u v, v}}
    (h : ∀ i : I, R ⟶ F i)
    (u : R ⟶ indexedProd F)
    (hu : ∀ i : I, u ≫ indexedProdProj F i = h i) :
    u = indexedProdLift F h := by
  apply (homIndexedProdEquiv R F).injective
  funext i
  calc
    (homIndexedProdEquiv R F) u i
        = u ≫ indexedProdProj F i := by
            rfl
    _ = h i := hu i
    _ = (homIndexedProdEquiv R F) (indexedProdLift F h) i := by
          symm
          exact indexedProdLift_proj F h i

/-
==============================================================================
Project-local indexed-product predicate
==============================================================================
-/

/--
`IsIndexedProduct F P π` says that `P`, equipped with projections `π i`, is
an indexed product of the family `F`.
-/
structure IsIndexedProduct {I : Type v}
    (F : I → PolyC.{max u v, v})
    (Pprod : PolyC.{max u v, v})
    (π : ∀ i : I, Pprod ⟶ F i) : Prop where
  lift :
    ∀ {R : PolyC.{max u v, v}} (h : ∀ i : I, R ⟶ F i),
      ∃! u : R ⟶ Pprod, ∀ i : I, u ≫ π i = h i

/--
The explicit indexed product satisfies the project-local universal property.
-/
theorem indexedProd_isIndexedProduct {I : Type v}
    (F : I → PolyC.{max u v, v}) :
    IsIndexedProduct F (indexedProd F) (indexedProdProj F) := by
  refine ⟨?_⟩
  intro R h
  refine ⟨indexedProdLift F h, ?factorization, ?uniqueness⟩
  · intro i
    exact indexedProdLift_proj F h i
  · intro u hu
    exact indexedProdLift_unique F h u hu

/-
==============================================================================
Semantic behavior of indexed products
==============================================================================

Evaluation sends the indexed product object to the indexed product of the
evaluations. This is the Type-level counterpart of pointwise products of
functors.
-/

/--
Evaluation of an indexed product is the indexed product of evaluations.
-/
def evalIndexedProdEquiv {I : Type v}
    (F : I → PolyC.{max u v, v}) (X : Type w) :
    (indexedProd F).eval X ≃ (∀ i : I, (F i).eval X) where
  toFun z := fun i => ⟨z.1 i, fun d => z.2 ⟨i, d⟩⟩
  invFun xs :=
    ⟨fun i => (xs i).1,
      fun d => (xs d.1).2 d.2⟩
  left_inv := by
    intro z
    rcases z with ⟨a, fill⟩
    apply Sigma.ext
    · funext i
      rfl
    · apply heq_of_eq
      funext d
      cases d with
      | mk i dir => rfl
  right_inv := by
    intro xs
    funext i
    /-
    This is a Sigma-eta step.

    The left-hand side has been rebuilt as

      ⟨(xs i).1, fun d => (xs i).2 d⟩,

    which is propositionally equal to `xs i`, but not always solved by raw
    `rfl` because the second component is a function in a dependent pair.
    -/
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext d
      rfl

/--
Under `evalIndexedProdEquiv`, the `i`th component is evaluation of the `i`th
projection.
-/
theorem evalIndexedProdEquiv_proj {I : Type v}
    (F : I → PolyC.{max u v, v}) (X : Type w)
    (z : (indexedProd F).eval X) (i : I) :
    evalIndexedProdEquiv F X z i
      =
    PolyC.map (indexedProdProj F i) (X := X) z := by
  rcases z with ⟨a, fill⟩
  rfl

/--
The inverse of `evalIndexedProdEquiv` has the expected semantic projections.
-/
theorem evalIndexedProdEquiv_symm_proj {I : Type v}
    (F : I → PolyC.{max u v, v}) (X : Type w)
    (xs : ∀ i : I, (F i).eval X) (i : I) :
    PolyC.map (indexedProdProj F i) (X := X)
        ((evalIndexedProdEquiv F X).symm xs)
      =
    xs i := by
  exact congrArg (fun k => k i) ((evalIndexedProdEquiv F X).right_inv xs)

end PolyC
