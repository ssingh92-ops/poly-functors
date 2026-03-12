/-
============================================================
EE598 — Poly Project
File: Poly/Universal.lean
============================================================

## Purpose (human-readable)
This file proves that our `sum` and `prod` constructions are not merely
syntactic constructors, but satisfy the *universal properties* of:

  • coproduct (categorical sum)  in PolyC
  • product   (categorical product) in PolyC

That is: they are characterized by how morphisms *to/from them* behave.

------------------------------------------------------------
COPRODUCT (sum)
------------------------------------------------------------

For objects P, Q, the coproduct P ⊔ Q comes with injections:

  ι₁ : P ⟶ (P ⊔ Q)
  ι₂ : Q ⟶ (P ⊔ Q)

and satisfies:
  For any R, giving h : (P ⊔ Q) ⟶ R is equivalent to giving:
    f : P ⟶ R   and   g : Q ⟶ R

In symbols:
  Hom(P ⊔ Q, R) ≃ Hom(P, R) × Hom(Q, R)

In our file:
  - `sum` is the object (already defined in Poly/SumProd.lean)
  - `coprodInl`, `coprodInr` are injections
  - `coprodDesc` is the “copairing” / case analysis map out of the sum
  - `homSumEquiv` packages the universal property as an Equiv

------------------------------------------------------------
PRODUCT (prod)
------------------------------------------------------------

For objects P, Q, the product P × Q comes with projections:

  π₁ : (P × Q) ⟶ P
  π₂ : (P × Q) ⟶ Q

and satisfies:
  For any R, giving h : R ⟶ (P × Q) is equivalent to giving:
    f : R ⟶ P   and   g : R ⟶ Q

In symbols:
  Hom(R, P × Q) ≃ Hom(R, P) × Hom(R, Q)

In our file:
  - `prod` is the object (already defined in Poly/SumProd.lean)
  - `prodFst`, `prodSnd` are projections
  - `prodLift` is the pairing map into the product
  - `homProdEquiv` packages the universal property as an Equiv

## Why this matters for the rest of the project
Once we have universal properties, we can:
- build categorical structure (limits/colimits)
- prove monoidal/coherence statements using these universal properties
- prepare for “big book” goals like cartesian closedness or equalizers

============================================================
-/
import Poly.SumProd

universe u v
open CategoryTheory

namespace PolyC

/-
============================================================
Coproduct structure for `sum`
============================================================
-/

/-- Left injection ι₁ : P ⟶ (P ⊔ Q). -/
def coprodInl (P Q : PolyC.{u, v}) : P ⟶ sum P Q where
  onShapes := fun a => Sum.inl a
  onPos := fun _ p => p

/-- Right injection ι₂ : Q ⟶ (P ⊔ Q). -/
def coprodInr (P Q : PolyC.{u, v}) : Q ⟶ sum P Q where
  onShapes := fun b => Sum.inr b
  onPos := fun _ p => p

/--
Case analysis / copairing:

Given f : P ⟶ R and g : Q ⟶ R, produce:
  [f,g] : (P ⊔ Q) ⟶ R
-/
def coprodDesc {P Q R : PolyC.{u, v}} (f : P ⟶ R) (g : Q ⟶ R) : (sum P Q) ⟶ R where
  onShapes := fun s => Sum.casesOn s f.onShapes g.onShapes
  onPos := fun s =>
    match s with
    | Sum.inl a => fun rpos => f.onPos a rpos
    | Sum.inr b => fun rpos => g.onPos b rpos

/-- Computation rule: ι₁ ≫ [f,g] = f. -/
theorem coprodInl_desc {P Q R : PolyC.{u, v}} (f : P ⟶ R) (g : Q ⟶ R) :
    (coprodInl P Q ≫ coprodDesc f g) = f := by
  apply Hom.ext
  · funext a
    rfl
  · intro a
    apply heq_of_eq
    funext rpos
    rfl

/-- Computation rule: ι₂ ≫ [f,g] = g. -/
theorem coprodInr_desc {P Q R : PolyC.{u, v}} (f : P ⟶ R) (g : Q ⟶ R) :
    (coprodInr P Q ≫ coprodDesc f g) = g := by
  apply Hom.ext
  · funext b
    rfl
  · intro b
    apply heq_of_eq
    funext rpos
    rfl

/--
Universal property packaged as an explicit equivalence:

  Hom(P ⊔ Q, R) ≃ Hom(P, R) × Hom(Q, R)
-/
def homSumEquiv (P Q R : PolyC.{u, v}) :
    ((sum P Q) ⟶ R) ≃ (P ⟶ R) × (Q ⟶ R) where
  toFun h := (coprodInl P Q ≫ h, coprodInr P Q ≫ h)
  invFun fg := coprodDesc (P := P) (Q := Q) (R := R) fg.1 fg.2
  left_inv := by
    intro h
    -- Show: coprodDesc (ι₁≫h) (ι₂≫h) = h
    apply Hom.ext
    · funext s
      cases s with
      | inl a => rfl
      | inr b => rfl
    · intro s
      cases s with
      | inl a =>
          apply heq_of_eq
          funext rpos
          rfl
      | inr b =>
          apply heq_of_eq
          funext rpos
          rfl
  right_inv := by
    rintro ⟨f, g⟩
    -- Reduce to the two computation rules
    have h1 : (coprodInl P Q ≫ coprodDesc f g) = f := coprodInl_desc (P := P) (Q := Q) (R := R) f g
    have h2 : (coprodInr P Q ≫ coprodDesc f g) = g := coprodInr_desc (P := P) (Q := Q) (R := R) f g
    cases h1
    cases h2
    rfl

/-
============================================================
Product structure for `prod`
============================================================
-/

/-- First projection π₁ : (P × Q) ⟶ P. -/
def prodFst (P Q : PolyC.{u, v}) : (prod P Q) ⟶ P where
  onShapes := fun ab => ab.1
  onPos := fun _ ppos => Sum.inl ppos

/-- Second projection π₂ : (P × Q) ⟶ Q. -/
def prodSnd (P Q : PolyC.{u, v}) : (prod P Q) ⟶ Q where
  onShapes := fun ab => ab.2
  onPos := fun _ qpos => Sum.inr qpos

/--
Pairing / product-lift:

Given f : R ⟶ P and g : R ⟶ Q, produce:
  ⟨f,g⟩ : R ⟶ (P × Q)
-/
def prodLift {R P Q : PolyC.{u, v}} (f : R ⟶ P) (g : R ⟶ Q) : R ⟶ (prod P Q) where
  onShapes := fun r => (f.onShapes r, g.onShapes r)
  onPos := fun r s =>
    match s with
    | Sum.inl ppos => f.onPos r ppos
    | Sum.inr qpos => g.onPos r qpos

/-- Computation rule: ⟨f,g⟩ ≫ π₁ = f. -/
theorem prodLift_fst {R P Q : PolyC.{u, v}} (f : R ⟶ P) (g : R ⟶ Q) :
    (prodLift (R := R) (P := P) (Q := Q) f g ≫ prodFst P Q) = f := by
  apply Hom.ext
  · funext r
    rfl
  · intro r
    apply heq_of_eq
    funext ppos
    rfl

/-- Computation rule: ⟨f,g⟩ ≫ π₂ = g. -/
theorem prodLift_snd {R P Q : PolyC.{u, v}} (f : R ⟶ P) (g : R ⟶ Q) :
    (prodLift (R := R) (P := P) (Q := Q) f g ≫ prodSnd P Q) = g := by
  apply Hom.ext
  · funext r
    rfl
  · intro r
    apply heq_of_eq
    funext qpos
    rfl

/--
Universal property packaged as an explicit equivalence:

  Hom(R, P × Q) ≃ Hom(R, P) × Hom(R, Q)
-/
def homProdEquiv (R P Q : PolyC.{u, v}) :
    (R ⟶ (prod P Q)) ≃ (R ⟶ P) × (R ⟶ Q) where
  toFun h := (h ≫ prodFst P Q, h ≫ prodSnd P Q)
  invFun fg := prodLift (R := R) (P := P) (Q := Q) fg.1 fg.2
  left_inv := by
    intro h
    -- IMPORTANT: force the arrow type `R ⟶ prod P Q` to unfold to our structure `PolyC.Hom`.
    change PolyC.Hom R (prod P Q) at h
    -- Now we can destructure `h` as the structure it really is.
    cases h with
    | mk hShapes hPos =>
      apply PolyC.Hom.ext
      · funext r
        -- now `hShapes r : P.A × Q.A`, so split it
        cases hShapes r with
        | mk a b => rfl
      · intro r
        apply heq_of_eq
        funext s
        cases s <;> rfl
  right_inv := by
    rintro ⟨f, g⟩
    have h1 : (prodLift (R := R) (P := P) (Q := Q) f g ≫ prodFst P Q) = f :=
      prodLift_fst (R := R) (P := P) (Q := Q) f g
    have h2 : (prodLift (R := R) (P := P) (Q := Q) f g ≫ prodSnd P Q) = g :=
      prodLift_snd (R := R) (P := P) (Q := Q) f g
    cases h1
    cases h2
    rfl

end PolyC
