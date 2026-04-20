import Poly.Core

/-
============================================================
EE598 — Poly Project
File: Poly/IndexedCoproducts.lean
============================================================

This file constructs indexed coproducts in the category `PolyC` of
polynomial functors / containers.

Book motivation:
Chapter 1 reviews indexed coproducts of sets as dependent sums. Chapter 5
then uses coproducts as one of the ingredients for constructing colimits
in `Poly`.

For an indexed family of polynomials

  F : I → PolyC,

the coproduct object has:

  positions:
    a choice of an index together with a position in that factor,

      Σ i : I, (F i).A,

  directions at a position `(i, a)`:
    exactly the directions of the selected factor at the selected position,

      (F i).B a.

This is the indexed version of the binary coproduct already implemented in
`Poly/Universal.lean`, where binary coproduct positions are a sum and the
directions are inherited from the chosen summand.

Universe note:
The index type contributes to the position type

  Σ i : I, (F i).A.

So, in this homogeneous Type-level presentation, we state the construction
for

  I : Type u
  F : I → PolyC.{u, v}

and obtain an object again in `PolyC.{u, v}`.

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
Indexed coproduct object
==============================================================================
-/

/--
The indexed coproduct of a family of polynomial functors.

A position is a choice of an index and then a position in that indexed factor.
The directions at such a position are the directions of the selected factor.
-/
def indexedCoprod {I : Type u} (F : I → PolyC.{u, v}) : PolyC.{u, v} where
  A := Sigma (fun i : I => (F i).A)
  B := fun ia => (F ia.1).B ia.2

/--
The positions of an indexed coproduct are the indexed coproduct of positions.
This is definitional, but the explicit equivalence is useful as a named API.
-/
def indexedCoprodPositionsEquiv {I : Type u} (F : I → PolyC.{u, v}) :
    (indexedCoprod F).A ≃ Sigma (fun i : I => (F i).A) :=
  Equiv.refl _

/--
The directions of an indexed coproduct are inherited from the selected factor.
-/
def indexedCoprodDirectionsEquiv {I : Type u}
    (F : I → PolyC.{u, v})
    (ia : (indexedCoprod F).A) :
    (indexedCoprod F).B ia ≃ (F ia.1).B ia.2 :=
  Equiv.refl _

/-
==============================================================================
Coproduct injections
==============================================================================
-/

/--
Injection of the `i`th factor into the indexed coproduct.
-/
def indexedCoprodIn {I : Type u}
    (F : I → PolyC.{u, v}) (i : I) :
    F i ⟶ indexedCoprod F where
  onShapes := fun a => ⟨i, a⟩
  onPos := fun _ d => d

/-
==============================================================================
Universal map out of an indexed coproduct
==============================================================================
-/

/--
Given maps from every summand into a target `R`, build the induced map out of
the indexed coproduct.
-/
def indexedCoprodDesc {I : Type u}
    (F : I → PolyC.{u, v})
    {R : PolyC.{u, v}}
    (h : ∀ i : I, F i ⟶ R) :
    indexedCoprod F ⟶ R where
  onShapes := fun ia => (h ia.1).onShapes ia.2
  onPos := fun ia rdir => (h ia.1).onPos ia.2 rdir

/--
The copairing map restricts to the original map on the `i`th summand.
-/
theorem indexedCoprodIn_desc {I : Type u}
    (F : I → PolyC.{u, v})
    {R : PolyC.{u, v}}
    (h : ∀ i : I, F i ⟶ R) (i : I) :
    indexedCoprodIn F i ≫ indexedCoprodDesc F h = h i := by
  apply Hom.ext
  · funext a
    rfl
  · intro a
    apply heq_of_eq
    funext rdir
    rfl

/-
==============================================================================
Universal property as an equivalence of hom-types
==============================================================================
-/

/--
Universal property of the indexed coproduct, packaged as an explicit
equivalence:

  Hom(Σᵢ F i, R) ≃ Πᵢ Hom(F i, R).
-/
def homIndexedCoprodEquiv {I : Type u}
    (F : I → PolyC.{u, v})
    (R : PolyC.{u, v}) :
    (indexedCoprod F ⟶ R) ≃ (∀ i : I, F i ⟶ R) where
  toFun h := fun i => indexedCoprodIn F i ≫ h
  invFun h := indexedCoprodDesc F h
  left_inv := by
    intro h
    change PolyC.Hom (indexedCoprod F) R at h
    cases h with
    | mk hShapes hPos =>
        apply Hom.ext
        · funext ia
          cases ia with
          | mk i a => rfl
        · intro ia
          cases ia with
          | mk i a =>
              apply heq_of_eq
              funext rdir
              rfl
  right_inv := by
    intro h
    funext i
    exact indexedCoprodIn_desc F h i

/--
Eta rule for maps out of an indexed coproduct.
-/
theorem indexedCoprod_eta {I : Type u}
    (F : I → PolyC.{u, v})
    {R : PolyC.{u, v}}
    (h : indexedCoprod F ⟶ R) :
    indexedCoprodDesc F (fun i => indexedCoprodIn F i ≫ h) = h := by
  exact (homIndexedCoprodEquiv F R).left_inv h

/--
Uniqueness for maps out of an indexed coproduct.
-/
theorem indexedCoprodDesc_unique {I : Type u}
    (F : I → PolyC.{u, v})
    {R : PolyC.{u, v}}
    (h : ∀ i : I, F i ⟶ R)
    (u : indexedCoprod F ⟶ R)
    (hu : ∀ i : I, indexedCoprodIn F i ≫ u = h i) :
    u = indexedCoprodDesc F h := by
  apply (homIndexedCoprodEquiv F R).injective
  funext i
  calc
    (homIndexedCoprodEquiv F R) u i
        = indexedCoprodIn F i ≫ u := by
            rfl
    _ = h i := hu i
    _ = (homIndexedCoprodEquiv F R) (indexedCoprodDesc F h) i := by
          symm
          exact indexedCoprodIn_desc F h i

/-
==============================================================================
Project-local indexed-coproduct predicate
==============================================================================
-/

/--
`IsIndexedCoproduct F C ι` says that `C`, equipped with injections `ι i`, is
an indexed coproduct of the family `F`.
-/
structure IsIndexedCoproduct {I : Type u}
    (F : I → PolyC.{u, v})
    (C : PolyC.{u, v})
    (ι : ∀ i : I, F i ⟶ C) : Prop where
  desc :
    ∀ {R : PolyC.{u, v}} (h : ∀ i : I, F i ⟶ R),
      ∃! u : C ⟶ R, ∀ i : I, ι i ≫ u = h i

/--
The explicit indexed coproduct satisfies the project-local universal property.
-/
theorem indexedCoprod_isIndexedCoproduct {I : Type u}
    (F : I → PolyC.{u, v}) :
    IsIndexedCoproduct F (indexedCoprod F) (indexedCoprodIn F) := by
  refine ⟨?_⟩
  intro R h
  refine ⟨indexedCoprodDesc F h, ?factorization, ?uniqueness⟩
  · intro i
    exact indexedCoprodIn_desc F h i
  · intro u hu
    exact indexedCoprodDesc_unique F h u hu

/-
==============================================================================
Semantic behavior of indexed coproducts
==============================================================================

Evaluation sends the indexed coproduct object to the indexed coproduct of the
evaluations. This is the Type-level counterpart of pointwise coproducts of
functors.
-/

/--
Evaluation of an indexed coproduct is the indexed coproduct of evaluations.
-/
def evalIndexedCoprodEquiv {I : Type u}
    (F : I → PolyC.{u, v}) (X : Type w) :
    (indexedCoprod F).eval X ≃ Sigma (fun i : I => (F i).eval X) where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv := by
    intro z
    rcases z with ⟨ia, fill⟩
    cases ia with
    | mk i a => rfl
  right_inv := by
    intro z
    rcases z with ⟨i, x⟩
    rcases x with ⟨a, fill⟩
    rfl

/--
Under `evalIndexedCoprodEquiv`, evaluation of the `i`th injection is the
inclusion of the `i`th semantic summand.
-/
theorem evalIndexedCoprodEquiv_in {I : Type u}
    (F : I → PolyC.{u, v}) (X : Type w)
    (i : I) (z : (F i).eval X) :
    evalIndexedCoprodEquiv F X
        (PolyC.map (indexedCoprodIn F i) (X := X) z)
      =
    ⟨i, z⟩ := by
  rcases z with ⟨a, fill⟩
  rfl

/--
The inverse of `evalIndexedCoprodEquiv` sends a semantic summand inclusion to
semantic evaluation of the corresponding coproduct injection.
-/
theorem evalIndexedCoprodEquiv_symm_in {I : Type u}
    (F : I → PolyC.{u, v}) (X : Type w)
    (i : I) (z : (F i).eval X) :
    (evalIndexedCoprodEquiv F X).symm ⟨i, z⟩
      =
    PolyC.map (indexedCoprodIn F i) (X := X) z := by
  rcases z with ⟨a, fill⟩
  rfl

end PolyC
