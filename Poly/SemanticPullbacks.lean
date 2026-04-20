import Poly.Pullbacks
import Poly.SemanticEqualizers

/-
============================================================
EE598 — Poly Project
File: Poly/SemanticPullbacks.lean
============================================================

This file proves the pointwise semantic pullback theorem for the explicit
pullbacks constructed in `Poly/Pullbacks.lean`.

Book statement behind the construction:
limits in the functor category `Set^Set` are computed pointwise. Since the
book also shows that the pullback in `Poly` can be obtained from products
and equalizers, the semantic interpretation of a pullback should be the
ordinary pullback of the interpreted component functions at each type `X`.

In this project, `PullObj f g` is defined as the equalizer of the two
comparison maps out of the product:

  prod P Q ⇉ S

namely

  pullLeft  f g = prodFst P Q ≫ f,
  pullRight f g = prodSnd P Q ≫ g.

So the semantic proof follows the same route:

  1. evaluation of products is identified by `evalProdEquiv`,
  2. the semantic equalizer theorem from `Poly/SemanticEqualizers.lean`
     applies to `pullLeft f g` and `pullRight f g`,
  3. the resulting equalizer property is repackaged as the ordinary
     function-level pullback universal property.

This file does not rebuild pullbacks, products, or equalizers. It only proves
that the already-constructed pullback object evaluates pointwise as a
pullback of types.

Terminology note:
the codebase still uses the field names `A`, `B`, `onShapes`, and `onPos`.
Mathematically these mean:

  • `A`        = positions,
  • `B a`      = directions at position `a`,
  • `onShapes` = forward map on positions,
  • `onPos`    = backward pullback map on directions.
============================================================
-/

open CategoryTheory

namespace PolyC

universe u v w

/-
==============================================================================
A lightweight function-level pullback predicate
==============================================================================

This is the Type-level analogue of the project-local categorical predicate
`IsPullback` from `Poly/Pullbacks.lean`.
-/

/--
`IsFunctionPullback f g π₁ π₂` says that the square of functions

  E --π₂--> B
  |        |
  π₁       g
  v        v
  A --f--> C

is a pullback square in the category of types and functions.
-/
structure IsFunctionPullback
    {A : Type _} {B : Type _} {C : Type _} {E : Type _}
    (f : A → C) (g : B → C)
    (π₁ : E → A) (π₂ : E → B) : Prop where
  condition : f ∘ π₁ = g ∘ π₂
  lift :
    ∀ {R : Type w} (a : R → A) (b : R → B),
      f ∘ a = g ∘ b →
      ∃! u : R → E, π₁ ∘ u = a ∧ π₂ ∘ u = b

section SemanticPullback

variable {P Q S : PolyC.{u, v}} (f : P ⟶ S) (g : Q ⟶ S)

/-
==============================================================================
Product-evaluation compatibility lemmas
==============================================================================

The explicit product object satisfies

  (prod P Q).eval X ≃ P.eval X × Q.eval X.

The lemmas below record how this equivalence interacts with the product
projections and with the two comparison maps used to define `PullObj f g`.
They are intentionally small and computational: each proof just unfolds the
container semantics of products.
-/

/-- Under `evalProdEquiv`, the first product projection is the first component. -/
theorem evalProdEquiv_fst (X : Type v)
    (z : (prod P Q).eval X) :
    (evalProdEquiv P Q X z).1
      =
    PolyC.map (prodFst P Q) (X := X) z := by
  rcases z with ⟨⟨p, q⟩, fill⟩
  rfl

/-- Under `evalProdEquiv`, the second product projection is the second component. -/
theorem evalProdEquiv_snd (X : Type v)
    (z : (prod P Q).eval X) :
    (evalProdEquiv P Q X z).2
      =
    PolyC.map (prodSnd P Q) (X := X) z := by
  rcases z with ⟨⟨p, q⟩, fill⟩
  rfl

/-- The semantic first projection of an explicitly paired product point. -/
theorem evalProdEquiv_symm_fst (X : Type v)
    (xP : P.eval X) (xQ : Q.eval X) :
    PolyC.map (prodFst P Q) (X := X)
        ((evalProdEquiv P Q X).symm (xP, xQ))
      =
    xP := by
  rcases xP with ⟨p, fillP⟩
  rcases xQ with ⟨q, fillQ⟩
  rfl

/-- The semantic second projection of an explicitly paired product point. -/
theorem evalProdEquiv_symm_snd (X : Type v)
    (xP : P.eval X) (xQ : Q.eval X) :
    PolyC.map (prodSnd P Q) (X := X)
        ((evalProdEquiv P Q X).symm (xP, xQ))
      =
    xQ := by
  rcases xP with ⟨p, fillP⟩
  rcases xQ with ⟨q, fillQ⟩
  rfl

/--
Evaluating the first comparison map on an explicitly paired product point
amounts to applying `f` to the first component.
-/
theorem eval_pullLeft_pair (X : Type v)
    (xP : P.eval X) (xQ : Q.eval X) :
    PolyC.map (pullLeft f g) (X := X)
        ((evalProdEquiv P Q X).symm (xP, xQ))
      =
    PolyC.map f (X := X) xP := by
  rcases xP with ⟨p, fillP⟩
  rcases xQ with ⟨q, fillQ⟩
  rfl

/--
Evaluating the second comparison map on an explicitly paired product point
amounts to applying `g` to the second component.
-/
theorem eval_pullRight_pair (X : Type v)
    (xP : P.eval X) (xQ : Q.eval X) :
    PolyC.map (pullRight f g) (X := X)
        ((evalProdEquiv P Q X).symm (xP, xQ))
      =
    PolyC.map g (X := X) xQ := by
  rcases xP with ⟨p, fillP⟩
  rcases xQ with ⟨q, fillQ⟩
  rfl

/--
The first semantic pullback projection is the first product projection after
mapping into the product.
-/
theorem eval_pullFst_as_prodFst (X : Type v)
    (z : (PullObj f g).eval X) :
    PolyC.map (pullFst f g) (X := X) z
      =
    PolyC.map (prodFst P Q) (X := X)
      (PolyC.map (pullToProd f g) (X := X) z) := by
  rcases z with ⟨p, fill⟩
  rfl

/--
The second semantic pullback projection is the second product projection after
mapping into the product.
-/
theorem eval_pullSnd_as_prodSnd (X : Type v)
    (z : (PullObj f g).eval X) :
    PolyC.map (pullSnd f g) (X := X) z
      =
    PolyC.map (prodSnd P Q) (X := X)
      (PolyC.map (pullToProd f g) (X := X) z) := by
  rcases z with ⟨p, fill⟩
  rfl

/-
==============================================================================
The semantic pullback theorem
==============================================================================
-/

/--
For each type `X`, the evaluated pullback square is a pullback square of
ordinary functions.
-/
theorem eval_pullback_isPullback (X : Type v) :
    IsFunctionPullback
      (PolyC.map f (X := X))
      (PolyC.map g (X := X))
      (PolyC.map (pullFst f g) (X := X))
      (PolyC.map (pullSnd f g) (X := X)) := by
  refine ⟨?condition, ?lift⟩
  · -- The evaluated square commutes.
    funext z
    have hz :
        PolyC.map (pullFst f g ≫ f) (X := X) z
          =
        PolyC.map (pullSnd f g ≫ g) (X := X) z := by
      exact congrArg
        (fun k : PullObj f g ⟶ S => PolyC.map k (X := X) z)
        (pullback_condition f g)
    simpa [Function.comp, PolyC.map, PolyC.comp] using hz
  · -- Universal property of the evaluated pullback.
    intro R a b h
    -- First package the two component maps as a map into the evaluated product.
    let pair : R → (prod P Q).eval X := fun r =>
      (evalProdEquiv P Q X).symm (a r, b r)
    -- The commutativity assumption says that this product-valued map equalizes
    -- the two comparison maps defining the pullback object.
    have pair_equalizes :
        (PolyC.map (pullLeft f g) (X := X)) ∘ pair
          =
        (PolyC.map (pullRight f g) (X := X)) ∘ pair := by
      funext r
      have hr :
          PolyC.map f (X := X) (a r)
            =
          PolyC.map g (X := X) (b r) := by
        simpa [Function.comp] using congrArg (fun k => k r) h
      calc
        PolyC.map (pullLeft f g) (X := X) (pair r)
            = PolyC.map f (X := X) (a r) := by
                exact eval_pullLeft_pair (f := f) (g := g) X (a r) (b r)
        _ = PolyC.map g (X := X) (b r) := hr
        _ = PolyC.map (pullRight f g) (X := X) (pair r) := by
              symm
              exact eval_pullRight_pair (f := f) (g := g) X (a r) (b r)
    -- Since `PullObj f g` is an equalizer of `pullLeft f g` and
    -- `pullRight f g`, the semantic equalizer theorem gives a unique lift.
    rcases
      (eval_eq_isEqualizer
        (f := pullLeft f g)
        (g := pullRight f g)
        (X := X))
      with ⟨_eqCondition, eqLift⟩
    rcases eqLift pair pair_equalizes with ⟨u, hu, hUnique⟩
    refine ⟨u, ?factorization, ?uniqueness⟩
    · -- The lift has the requested first and second projections.
      constructor
      · funext r
        have hToProd :
            PolyC.map (pullToProd f g) (X := X) (u r) = pair r := by
          exact congrArg (fun k => k r) hu
        calc
          PolyC.map (pullFst f g) (X := X) (u r)
              = PolyC.map (prodFst P Q) (X := X)
                  (PolyC.map (pullToProd f g) (X := X) (u r)) := by
                    exact eval_pullFst_as_prodFst (f := f) (g := g) X (u r)
          _ = PolyC.map (prodFst P Q) (X := X) (pair r) := by
                rw [hToProd]
          _ = a r := by
                dsimp [pair]
                exact evalProdEquiv_symm_fst (P := P) (Q := Q) X (a r) (b r)
      · funext r
        have hToProd :
            PolyC.map (pullToProd f g) (X := X) (u r) = pair r := by
          exact congrArg (fun k => k r) hu
        calc
          PolyC.map (pullSnd f g) (X := X) (u r)
              = PolyC.map (prodSnd P Q) (X := X)
                  (PolyC.map (pullToProd f g) (X := X) (u r)) := by
                    exact eval_pullSnd_as_prodSnd (f := f) (g := g) X (u r)
          _ = PolyC.map (prodSnd P Q) (X := X) (pair r) := by
                rw [hToProd]
          _ = b r := by
                dsimp [pair]
                exact evalProdEquiv_symm_snd (P := P) (Q := Q) X (a r) (b r)
    · -- Any other map with the same two projections is equal to the lift.
      intro u' hu'
      have huProd :
          (PolyC.map (pullToProd f g) (X := X)) ∘ u' = pair := by
        funext r
        apply (evalProdEquiv P Q X).injective
        dsimp [pair]
        rw [(evalProdEquiv P Q X).apply_symm_apply (a r, b r)]
        apply Prod.ext
        · calc
            (evalProdEquiv P Q X
              (PolyC.map (pullToProd f g) (X := X) (u' r))).1
                = PolyC.map (prodFst P Q) (X := X)
                    (PolyC.map (pullToProd f g) (X := X) (u' r)) := by
                      exact evalProdEquiv_fst (P := P) (Q := Q) X
                        (PolyC.map (pullToProd f g) (X := X) (u' r))
            _ = PolyC.map (pullFst f g) (X := X) (u' r) := by
                  symm
                  exact eval_pullFst_as_prodFst (f := f) (g := g) X (u' r)
            _ = a r := by
                  exact congrArg (fun k => k r) hu'.1
        · calc
            (evalProdEquiv P Q X
              (PolyC.map (pullToProd f g) (X := X) (u' r))).2
                = PolyC.map (prodSnd P Q) (X := X)
                    (PolyC.map (pullToProd f g) (X := X) (u' r)) := by
                      exact evalProdEquiv_snd (P := P) (Q := Q) X
                        (PolyC.map (pullToProd f g) (X := X) (u' r))
            _ = PolyC.map (pullSnd f g) (X := X) (u' r) := by
                  symm
                  exact eval_pullSnd_as_prodSnd (f := f) (g := g) X (u' r)
            _ = b r := by
                  exact congrArg (fun k => k r) hu'.2
      exact hUnique u' huProd

/--
The same theorem phrased using the semantic natural transformations supplied
by `Poly/Semantics.lean`.
-/
theorem homToNatTrans_app_isPullback (X : Type v) :
    IsFunctionPullback
      ((homToNatTrans (P := P) (Q := S) f).app X : P.eval X → S.eval X)
      ((homToNatTrans (P := Q) (Q := S) g).app X : Q.eval X → S.eval X)
      ((homToNatTrans
          (P := PullObj f g)
          (Q := P)
          (pullFst f g)).app X :
            (PullObj f g).eval X → P.eval X)
      ((homToNatTrans
          (P := PullObj f g)
          (Q := Q)
          (pullSnd f g)).app X :
            (PullObj f g).eval X → Q.eval X) := by
  simpa [homToNatTrans]
    using eval_pullback_isPullback (f := f) (g := g) X

end SemanticPullback

end PolyC
