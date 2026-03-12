/-
============================================================
EE598 — Poly Project
File: Poly/Semantics.lean
============================================================

This file is the bridge from “container polynomials” to “actual functors”.

- Every container polynomial P determines an endofunctor on Type:
      P.evalFunctor : Type ⥤ Type

- Every container morphism (lens) f : P ⟶ Q determines a natural transformation:
      homToNatTrans f : P.evalFunctor ⟶ Q.evalFunctor

- Bundled together, this becomes a functor:
      Sem : PolyC ⥤ (Type ⥤ Type)

NOTE (Lean detail):
`w` is a universe level, not an explicit parameter of `evalFunctor`,
so we must NOT write `evalFunctor (w := w)`.
We simply use dot-notation `P.evalFunctor`.
============================================================
-/
import Poly.Eval

universe u v w
open CategoryTheory

namespace PolyC

/-- Turn a container morphism into a natural transformation on evaluation functors. -/
def homToNatTrans {P Q : PolyC.{u, v}} (f : Hom P Q) :
    P.evalFunctor ⟶ Q.evalFunctor where
  app X := map f (X := X)
  naturality := by
    intro X Y h
    funext x
    cases x with
    | mk a fill => rfl

/--
Semantic interpretation functor:
  P ↦ P.evalFunctor
  f ↦ homToNatTrans f
-/
def Sem : PolyC.{u, v} ⥤ (Type w ⥤ Type (max u v w)) where
  obj P := P.evalFunctor
  map {P Q} f := homToNatTrans (P := P) (Q := Q) f
  map_id := by
    intro P
    apply CategoryTheory.NatTrans.ext
    funext X
    funext x
    cases x
    rfl
  map_comp := by
    intro P Q R f g
    apply CategoryTheory.NatTrans.ext
    funext X
    funext x
    cases x
    rfl

end PolyC
