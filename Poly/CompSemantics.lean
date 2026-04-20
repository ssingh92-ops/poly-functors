/-
============================================================
Poly Project
File: Poly/CompSemantics.lean
============================================================

## Goal
We already proved objectwise:
  (P ▷ Q)(X) ≃ P(Q(X))

Milestone 6 asks for the stronger categorical statement:
this equivalence is natural in X, i.e. it is a *natural isomorphism of functors*:

  (P ▷ Q).evalFunctor  ≅  Q.evalFunctor ⋙ P.evalFunctor

This makes the slogan precise:
  "evaluation sends ▷ to functor composition (up to iso)."

============================================================
-/
import Poly.Eval
import Poly.Composition
import Poly.CompOnMorphisms

universe u v w
open CategoryTheory

namespace PolyC

/--
Natural isomorphism:
  evalFunctor(P ▷ Q) ≅ (evalFunctor Q ⋙ evalFunctor P)
-/
def evalComposeIso (P Q : PolyC.{u, v}) :
    ( (P ▷ Q).evalFunctor ) ≅ (Q.evalFunctor ⋙ P.evalFunctor) :=
by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · -- component at X: the equivalence from Composition.lean turned into an Iso in Type
    refine
      { hom := (evalComposeEquiv P Q X).toFun
        inv := (evalComposeEquiv P Q X).invFun
        hom_inv_id := by
          funext x
          exact (evalComposeEquiv P Q X).left_inv x
        inv_hom_id := by
          funext x
          exact (evalComposeEquiv P Q X).right_inv x }
  · -- naturality
    intro X Y h
    funext x
    cases x with
    | mk s fill =>
      -- everything is definitional after expanding the constructions
      rfl

end PolyC
