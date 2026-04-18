import Poly.Equalizers
import Poly.Semantics

/-
============================================================
Poly Project
File: Poly/SemanticEqualizers.lean
============================================================

This file proves the pointwise semantic equalizer theorem suggested by
Exercise 5.43 in *Polynomial Functors*.

Book statement:
if

  e : E ⟶ P

is the equalizer of parallel arrows

  f g : P ⟶ Q

in `Poly`, then for every type `X` the induced function

  e_X : E(X) → P(X)

is the equalizer of the induced component functions

  f_X g_X : P(X) → Q(X).

We already constructed equalizers internally in `Poly/Equalizers.lean`.
The purpose of this file is to transport that universal property to
semantic interpretation.

Important project note:
we reuse the existing semantic layer from
  • `Poly/Eval.lean`
  • `Poly/Semantics.lean`

So this file does not re-prove functoriality of evaluation, and it does
not redefine `homToNatTrans`. It only adds the pointwise equalizer theorem.

Proof strategy:
The final proof follows the book directly rather than via a probing
polynomial. For a fixed type `X`, we consider the subtype

  { x : P.eval X // map f x = map g x }

of semantic elements of `P` on which the two component maps agree.
We then prove that `(EqObj f g).eval X` is explicitly equivalent to this
subtype:

  • a point of `(EqObj f g).eval X` gives a point of `P.eval X` by
    forgetting the equalizer proof on positions and composing with the
    quotient map on directions;
  • a point of `P.eval X` together with a proof that `map f` and `map g`
    agree gives an equalizer position, and the proof on the second
    component is exactly what is needed to descend the filling map
    through the direction quotient using `dirDesc`.

Once this equivalence is established, the function-level equalizer
universal property is immediate.

Mathematical context:
Exercise 5.43(1) asks for this componentwise equalizer theorem, and then
uses pointwise limits in `Set^Set` to identify equalizers in `Poly` with
those in the ambient functor category. :contentReference[oaicite:0]{index=0}
============================================================
-/

open CategoryTheory

namespace PolyC

universe u v w

/-
==============================================================================
A lightweight function-level equalizer predicate
==============================================================================

This is the Type-level analogue of the project-local categorical predicate
`IsEqualizer` from `Poly/Equalizers.lean`.

Important implementation note:
this predicate is intentionally universe-generic. In the direct semantic
proof below, there is no need to restrict the witness type `R` to the
positions universe of `P`; the earlier universe-restricted versions were
artifacts of a failed probe-based proof strategy.
-/

/--
`IsFunctionEqualizer f g e` says that `e : E → A` is an equalizer of the
parallel pair `f g : A → B` in the category of types and functions.
-/
def IsFunctionEqualizer {A : Type _} {B : Type _} {E : Type _}
    (f g : A → B) (e : E → A) : Prop :=
  f ∘ e = g ∘ e ∧
  ∀ {R : Type w} (h : R → A),
    f ∘ h = g ∘ h →
    ∃! u' : R → E, e ∘ u' = h

/-
==============================================================================
Pointwise semantic equalizers
==============================================================================
-/

section SemanticEqualizer

variable {P Q : PolyC.{u, v}} (f g : P ⟶ Q)

/--
The semantic equalizer at a fixed type `X`.

This is the subtype of semantic elements of `P` on which the two component
maps induced by `f` and `g` agree.
-/
abbrev PointEq (X : Type v) : Type (max u v) :=
  { x : P.eval X // map f x = map g x }

/-
==============================================================================
Helper for comparing semantic fillers across equal semantic points
==============================================================================

If two semantic elements are equal, then their filling maps agree on
heterogeneously equal directions.
-/

/--
Congruence for the filling map of a semantic element across propositionally
equal positions.
-/
private lemma evalFill_congr
    {R : PolyC.{u, v}} {X : Type v}
    {x y : R.eval X}
    (hxy : x = y)
    (qx : R.B x.1)
    (qy : R.B y.1)
    (hq : HEq qx qy) :
    x.2 qx = y.2 qy := by
  revert qx qy hq
  cases hxy
  intro qx qy hq
  cases hq
  rfl

/-
==============================================================================
From the internal semantic equalizer to the explicit equalizer subtype
==============================================================================
-/

/--
Send a semantic element of the internal equalizer object to the corresponding
semantic element of `P`, together with the proof that `map f` and `map g`
agree on it.
-/
def evalToPointEq (X : Type v) :
    (EqObj (f := f) (g := g)).eval X → PointEq (f := f) (g := g) X
  | z =>
      ⟨PolyC.map (eq (f := f) (g := g)) (X := X) z,
        by
          have hz :
              (PolyC.map ((eq (f := f) (g := g)) ≫ f) (X := X)) z
                =
              (PolyC.map ((eq (f := f) (g := g)) ≫ g) (X := X)) z := by
            exact congrArg
              (fun k : (EqObj (f := f) (g := g)) ⟶ Q =>
                (PolyC.map k (X := X)) z)
              (eq_comp_eq (f := f) (g := g))
          simpa [PolyC.comp, PolyC.map] using hz
      ⟩

/-
==============================================================================
From the explicit equalizer subtype back to the internal semantic equalizer
==============================================================================

This is the key book-facing construction.

Given
  x = (a, fill) : P.eval X
and a proof that
  map f x = map g x,
we obtain:

1. an equalizer position `aeq : EqA f g`, because the first projections agree;
2. a filling on the quotient directions, because equality of the second
   projections is exactly the coequalizer-respect condition needed by `dirDesc`.
-/

/--
Reconstruct a semantic element of the internal equalizer object from a point of
`P.eval X` on which the two component maps agree.
-/
def pointEqToEval (X : Type v) :
    PointEq (f := f) (g := g) X → (EqObj (f := f) (g := g)).eval X
  | ⟨⟨a, fill⟩, hEq⟩ =>
      let aeq : EqA (f := f) (g := g) := ⟨a, congrArg Sigma.fst hEq⟩
      ⟨aeq,
        dirDesc (f := f) (g := g) aeq
          (k := fill)
          (hk := by
            intro qf qg hq
            exact
              evalFill_congr
                (x := PolyC.map f (X := X) ⟨a, fill⟩)
                (y := PolyC.map g (X := X) ⟨a, fill⟩)
                hEq qf qg hq)
      ⟩

/-
==============================================================================
The two constructions are inverse
==============================================================================
-/

/--
Going from the internal semantic equalizer to the explicit subtype and back is
the identity.
-/
theorem pointEqToEval_evalToPointEq (X : Type v)
    (z : (EqObj (f := f) (g := g)).eval X) :
    pointEqToEval (f := f) (g := g) X (evalToPointEq (f := f) (g := g) X z) = z := by
  rcases z with ⟨a, fill⟩
  apply Sigma.ext
  · apply Subtype.ext
    rfl
  · apply heq_of_eq
    funext q
    refine Quot.inductionOn q ?_
    intro p
    rfl

/--
Going from the explicit subtype to the internal semantic equalizer and back is
the identity.
-/
theorem evalToPointEq_pointEqToEval (X : Type v)
    (z : PointEq (f := f) (g := g) X) :
    evalToPointEq (f := f) (g := g) X (pointEqToEval (f := f) (g := g) X z) = z := by
  rcases z with ⟨⟨a, fill⟩, hEq⟩
  apply Subtype.ext
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext p
    rfl

/--
Explicit equivalence between the semantic equalizer object and the subtype of
semantic points on which the component maps agree.
-/
def pointEqEquiv (X : Type v) :
    (EqObj (f := f) (g := g)).eval X ≃ PointEq (f := f) (g := g) X where
  toFun := evalToPointEq (f := f) (g := g) X
  invFun := pointEqToEval (f := f) (g := g) X
  left_inv := pointEqToEval_evalToPointEq (f := f) (g := g) X
  right_inv := evalToPointEq_pointEqToEval (f := f) (g := g) X

/-
==============================================================================
Pointwise semantic equalizers
==============================================================================

Now the universal property is straightforward: the explicit equalizer subtype is
obviously the equalizer in the category of types and functions, and the previous
equivalence identifies that subtype with `(EqObj f g).eval X`.
-/

/--
Exercise 5.43(1): for each `X : Type v`, the semantic map induced by the
internal equalizer lens is the equalizer of the semantic component maps.
-/
theorem eval_eq_isEqualizer (X : Type v) :
    IsFunctionEqualizer
      (PolyC.map f (X := X) : P.eval X → Q.eval X)
      (PolyC.map g (X := X) : P.eval X → Q.eval X)
      (PolyC.map (eq (f := f) (g := g)) (X := X) :
        (EqObj (f := f) (g := g)).eval X → P.eval X) := by
  refine ⟨?condition, ?lift⟩
  · funext z
    exact (evalToPointEq (f := f) (g := g) X z).2
  · intro R h heq
    let u : R → (EqObj (f := f) (g := g)).eval X :=
      fun r =>
        pointEqToEval (f := f) (g := g) X
          ⟨h r, congrArg (fun k => k r) heq⟩
    refine ⟨u, ?factorization, ?uniqueness⟩
    · funext r
      have hr :
          evalToPointEq (f := f) (g := g) X (u r)
            =
          ⟨h r, congrArg (fun k => k r) heq⟩ := by
        dsimp [u]
        exact
          evalToPointEq_pointEqToEval (f := f) (g := g) X
            ⟨h r, congrArg (fun k => k r) heq⟩
      exact congrArg Subtype.val hr
    · intro u' hu'
      funext r
      apply (pointEqEquiv (f := f) (g := g) X).injective
      have hu'_sub :
          (pointEqEquiv (f := f) (g := g) X) (u' r)
            =
          ⟨h r, congrArg (fun k => k r) heq⟩ := by
        apply Subtype.ext
        exact congrArg (fun k => k r) hu'
      have hu_sub :
          (pointEqEquiv (f := f) (g := g) X) (u r)
            =
          ⟨h r, congrArg (fun k => k r) heq⟩ := by
        dsimp [u, pointEqEquiv]
        exact
          evalToPointEq_pointEqToEval (f := f) (g := g) X
            ⟨h r, congrArg (fun k => k r) heq⟩
      exact hu'_sub.trans hu_sub.symm

/--
The same result phrased using the existing semantic natural transformations
from `Poly/Semantics.lean`.
-/
theorem homToNatTrans_app_isEqualizer (X : Type v) :
    IsFunctionEqualizer
      ((homToNatTrans (P := P) (Q := Q) f).app X : P.eval X → Q.eval X)
      ((homToNatTrans (P := P) (Q := Q) g).app X : P.eval X → Q.eval X)
      ((homToNatTrans
          (P := EqObj (f := f) (g := g))
          (Q := P)
          (eq (f := f) (g := g))).app X :
            (EqObj (f := f) (g := g)).eval X → P.eval X) := by
  simpa [homToNatTrans] using eval_eq_isEqualizer (f := f) (g := g) X

end SemanticEqualizer

end PolyC
