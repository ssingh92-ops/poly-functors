import Poly.Equalizers
import Poly.Universal

/-
============================================================
Poly/Pullbacks.lean
============================================================

This file constructs pullbacks in the category `PolyC` of polynomial
functors / containers.

Given a cospan

  P ⟶ S ⟵ Q

with maps

  f : P ⟶ S
  g : Q ⟶ S

a pullback is an object `E` together with maps

  π₁ : E ⟶ P
  π₂ : E ⟶ Q

such that the square commutes and is universal among commuting squares.

The construction used here is the standard categorical one:

  P ×[S] Q = Eq(P × Q ⇉ S).

The two maps from the product to the base are

  P × Q --π₁--> P --f--> S
  P × Q --π₂--> Q --g--> S.

This matches the book's limits story: products and equalizers generate
pullbacks, while the concrete positions-and-directions picture says that
pullbacks have pullbacks on positions and pushouts on directions.

Implementation note:
The definitions below take `f` and `g` as explicit parameters in every
construction. This is deliberate. If a definition is written using section
variables and one of the maps is unused in the body, Lean may omit that map
from the generated argument list. Then named applications such as
`(f := f)` and `(g := g)` become fragile. Here we avoid that by writing the
parameters explicitly and using positional application internally.
============================================================
-/

open CategoryTheory

namespace PolyC

universe u v

/--
`IsPullback f g π₁ π₂` says that the square

  E --π₂--> Q
  |        |
  π₁       g
  v        v
  P --f--> S

is a pullback square in `PolyC`.
-/
structure IsPullback
    {P Q S E : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (π₁ : E ⟶ P) (π₂ : E ⟶ Q) : Prop where
  condition : π₁ ≫ f = π₂ ≫ g
  lift :
    ∀ {R : PolyC.{u, v}} (a : R ⟶ P) (b : R ⟶ Q),
      a ≫ f = b ≫ g →
      ∃! u : R ⟶ E, u ≫ π₁ = a ∧ u ≫ π₂ = b

section PullbackConstruction

variable {P Q S : PolyC.{u, v}}

/-
==============================================================================
Step 1: The two comparison maps from the product to the base
==============================================================================
-/

/-- The first comparison map `P × Q ⟶ S`. -/
def pullLeft (f : P ⟶ S) (_g : Q ⟶ S) : prod P Q ⟶ S :=
  prodFst P Q ≫ f

/-- The second comparison map `P × Q ⟶ S`. -/
def pullRight (_f : P ⟶ S) (g : Q ⟶ S) : prod P Q ⟶ S :=
  prodSnd P Q ≫ g

/-
==============================================================================
Step 2: The pullback object
==============================================================================
-/

/-- The pullback object of `f : P ⟶ S` and `g : Q ⟶ S`. -/
def PullObj (f : P ⟶ S) (g : Q ⟶ S) : PolyC.{u, v} :=
  EqObj (f := pullLeft f g) (g := pullRight f g)

/-- The canonical map from the pullback object into the product `P × Q`. -/
def pullToProd (f : P ⟶ S) (g : Q ⟶ S) : PullObj f g ⟶ prod P Q :=
  eq (f := pullLeft f g) (g := pullRight f g)

/-
==============================================================================
Step 3: Pullback projections
==============================================================================
-/

/-- First pullback projection. -/
def pullFst (f : P ⟶ S) (g : Q ⟶ S) : PullObj f g ⟶ P :=
  pullToProd f g ≫ prodFst P Q

/-- Second pullback projection. -/
def pullSnd (f : P ⟶ S) (g : Q ⟶ S) : PullObj f g ⟶ Q :=
  pullToProd f g ≫ prodSnd P Q

/-
==============================================================================
Step 4: The pullback square commutes
==============================================================================
-/

/-- The square determined by `pullFst` and `pullSnd` commutes. -/
theorem pullback_condition (f : P ⟶ S) (g : Q ⟶ S) :
    pullFst f g ≫ f = pullSnd f g ≫ g := by
  change pullToProd f g ≫ pullLeft f g = pullToProd f g ≫ pullRight f g
  exact eq_comp_eq (f := pullLeft f g) (g := pullRight f g)

/-
==============================================================================
Step 5: Equalizing a product lift
==============================================================================

Given a commuting square into the cospan, the product map into `P × Q`
equalizes the two comparison maps to `S`.
-/

/-- The product lift of a commuting square equalizes the two comparison maps. -/
theorem prodLift_equalizes
    {R : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    prodLift (R := R) (P := P) (Q := Q) a b ≫ pullLeft f g
      =
    prodLift (R := R) (P := P) (Q := Q) a b ≫ pullRight f g := by
  calc
    prodLift (R := R) (P := P) (Q := Q) a b ≫ pullLeft f g
        = (prodLift (R := R) (P := P) (Q := Q) a b ≫ prodFst P Q) ≫ f := by
            rfl
    _ = a ≫ f := by
          rw [prodLift_fst (R := R) (P := P) (Q := Q) a b]
    _ = b ≫ g := h
    _ = (prodLift (R := R) (P := P) (Q := Q) a b ≫ prodSnd P Q) ≫ g := by
          rw [prodLift_snd (R := R) (P := P) (Q := Q) a b]
    _ = prodLift (R := R) (P := P) (Q := Q) a b ≫ pullRight f g := by
          rfl

/-
==============================================================================
Step 6: The universal lift into the pullback
==============================================================================
-/

/-- The induced map into the pullback from any commuting square. -/
def pullLift
    {R : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    R ⟶ PullObj f g :=
  eqLift
    (f := pullLeft f g)
    (g := pullRight f g)
    (prodLift (R := R) (P := P) (Q := Q) a b)
    (prodLift_equalizes f g a b h)

/--
The universal lift followed by the canonical map to the product is the original
product lift.
-/
theorem pullLift_toProd
    {R : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    pullLift f g a b h ≫ pullToProd f g
      =
    prodLift (R := R) (P := P) (Q := Q) a b := by
  refine PolyC.Hom.ext
    (pullLift f g a b h ≫ pullToProd f g)
    (prodLift (R := R) (P := P) (Q := Q) a b)
    ?hShapes ?hDirs
  · funext r
    rfl
  · intro r
    refine heq_of_eq ?_
    funext s
    rfl

/-- The universal lift has first projection `a`. -/
theorem pullLift_fst
    {R : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    pullLift f g a b h ≫ pullFst f g = a := by
  calc
    pullLift f g a b h ≫ pullFst f g
        = (pullLift f g a b h ≫ pullToProd f g) ≫ prodFst P Q := by
            rfl
    _ = prodLift (R := R) (P := P) (Q := Q) a b ≫ prodFst P Q := by
          rw [pullLift_toProd f g a b h]
    _ = a := by
          exact prodLift_fst (R := R) (P := P) (Q := Q) a b

/-- The universal lift has second projection `b`. -/
theorem pullLift_snd
    {R : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    pullLift f g a b h ≫ pullSnd f g = b := by
  calc
    pullLift f g a b h ≫ pullSnd f g
        = (pullLift f g a b h ≫ pullToProd f g) ≫ prodSnd P Q := by
            rfl
    _ = prodLift (R := R) (P := P) (Q := Q) a b ≫ prodSnd P Q := by
          rw [pullLift_toProd f g a b h]
    _ = b := by
          exact prodLift_snd (R := R) (P := P) (Q := Q) a b

/-- The two projection equations for the universal lift, packaged together. -/
theorem pullLift_factors
    {R : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g) :
    pullLift f g a b h ≫ pullFst f g = a
      ∧
    pullLift f g a b h ≫ pullSnd f g = b := by
  exact ⟨pullLift_fst f g a b h, pullLift_snd f g a b h⟩

/-
==============================================================================
Step 7: Product extensionality helper
==============================================================================
-/

/-- Extensionality for maps into the explicit product object. -/
private theorem prodHom_ext
    {R P Q : PolyC.{u, v}}
    {h k : R ⟶ prod P Q}
    (hfst : h ≫ prodFst P Q = k ≫ prodFst P Q)
    (hsnd : h ≫ prodSnd P Q = k ≫ prodSnd P Q) :
    h = k := by
  apply (homProdEquiv R P Q).injective
  change
    (h ≫ prodFst P Q, h ≫ prodSnd P Q)
      =
    (k ≫ prodFst P Q, k ≫ prodSnd P Q)
  exact Prod.ext hfst hsnd

/--
If a map into the pullback has projections `a` and `b`, then its composite
with `pullToProd` is the product lift `prodLift a b`.
-/
theorem pullToProd_eq_prodLift_of_projections
    {R : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (u : R ⟶ PullObj f g)
    (hu : u ≫ pullFst f g = a ∧ u ≫ pullSnd f g = b) :
    u ≫ pullToProd f g
      =
    prodLift (R := R) (P := P) (Q := Q) a b := by
  apply prodHom_ext
  · calc
      (u ≫ pullToProd f g) ≫ prodFst P Q
          = u ≫ pullFst f g := by
              rfl
      _ = a := hu.1
      _ = prodLift (R := R) (P := P) (Q := Q) a b ≫ prodFst P Q := by
            symm
            exact prodLift_fst (R := R) (P := P) (Q := Q) a b
  · calc
      (u ≫ pullToProd f g) ≫ prodSnd P Q
          = u ≫ pullSnd f g := by
              rfl
      _ = b := hu.2
      _ = prodLift (R := R) (P := P) (Q := Q) a b ≫ prodSnd P Q := by
            symm
            exact prodLift_snd (R := R) (P := P) (Q := Q) a b

/-
==============================================================================
Step 8: Uniqueness of the universal lift
==============================================================================
-/

/-- The universal lift into the pullback is unique. -/
theorem pullLift_unique
    {R : PolyC.{u, v}}
    (f : P ⟶ S) (g : Q ⟶ S)
    (a : R ⟶ P) (b : R ⟶ Q)
    (h : a ≫ f = b ≫ g)
    (u : R ⟶ PullObj f g)
    (hu : u ≫ pullFst f g = a ∧ u ≫ pullSnd f g = b) :
    u = pullLift f g a b h := by
  let hProd : R ⟶ prod P Q := prodLift (R := R) (P := P) (Q := Q) a b
  have hEq : hProd ≫ pullLeft f g = hProd ≫ pullRight f g := by
    exact prodLift_equalizes f g a b h
  have huProd : u ≫ pullToProd f g = hProd := by
    exact pullToProd_eq_prodLift_of_projections f g a b u hu
  have hliftProd : pullLift f g a b h ≫ pullToProd f g = hProd := by
    exact pullLift_toProd f g a b h
  rcases
    (eqObj_isEqualizer
      (f := pullLeft f g)
      (g := pullRight f g)).lift hProd hEq
    with ⟨w, hw, hwUnique⟩
  have hu_w : u = w := hwUnique u huProd
  have hlift_w : pullLift f g a b h = w :=
    hwUnique (pullLift f g a b h) hliftProd
  exact hu_w.trans hlift_w.symm

/-
==============================================================================
Step 9: The pullback universal property
==============================================================================
-/

/--
`PullObj f g`, with projections `pullFst` and `pullSnd`, satisfies the
pullback universal property.
-/
theorem pullObj_isPullback (f : P ⟶ S) (g : Q ⟶ S) :
    IsPullback f g (pullFst f g) (pullSnd f g) := by
  refine ⟨pullback_condition f g, ?_⟩
  intro R a b h
  refine ⟨pullLift f g a b h, ?factorization, ?uniqueness⟩
  · exact pullLift_factors f g a b h
  · intro u hu
    exact pullLift_unique f g a b h u hu

end PullbackConstruction

end PolyC
