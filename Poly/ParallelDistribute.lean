/-
Poly/ParallelDistribute.lean

Finish Milestone 5: prove ⊗ distributes over + in PolyC.

Lean engineering note:
For these isomorphisms, the position maps are literally identity functions,
but because they are dependent on the chosen shape, we must case-split on the
shape so the `B`-types reduce. After that, the required `HEq` goals are `rfl`.

So: no `heq_of_eq` needed.
-/
import Poly.SumProd
import Poly.Parallel

universe u v
open CategoryTheory

namespace PolyC

/-- Left distributivity: (P + Q) ⊗ R ≅ (P ⊗ R) + (Q ⊗ R). -/
def tensorSumLeftIso (P Q R : PolyC.{u, v}) :
    ((sum P Q) ⊗ R) ≅ (sum (P ⊗ R) (Q ⊗ R)) where
  hom :=
  { onShapes := fun sr =>
      match sr with
      | (Sum.inl a, r) => Sum.inl (a, r)
      | (Sum.inr b, r) => Sum.inr (b, r)
    onPos := by
      intro sr
      cases sr with
      | mk s r =>
        cases s with
        | inl a =>
            intro d; exact d
        | inr b =>
            intro d; exact d }
  inv :=
  { onShapes := fun t =>
      match t with
      | Sum.inl ar => (Sum.inl ar.1, ar.2)
      | Sum.inr br => (Sum.inr br.1, br.2)
    onPos := by
      intro t
      cases t with
      | inl ar =>
          intro d; exact d
      | inr br =>
          intro d; exact d }
  hom_inv_id := by
    apply Hom.ext
    · funext sr
      cases sr with
      | mk s r =>
        cases s <;> rfl
    · intro sr
      cases sr with
      | mk s r =>
        cases s <;> rfl
  inv_hom_id := by
    apply Hom.ext
    · funext t
      cases t <;> rfl
    · intro t
      cases t <;> rfl

/-- Right distributivity: P ⊗ (Q + R) ≅ (P ⊗ Q) + (P ⊗ R). -/
def tensorSumRightIso (P Q R : PolyC.{u, v}) :
    (P ⊗ (sum Q R)) ≅ (sum (P ⊗ Q) (P ⊗ R)) where
  hom :=
  { onShapes := fun ps =>
      match ps with
      | (p, Sum.inl b) => Sum.inl (p, b)
      | (p, Sum.inr c) => Sum.inr (p, c)
    onPos := by
      intro ps
      cases ps with
      | mk p s =>
        cases s with
        | inl b =>
            intro d; exact d
        | inr c =>
            intro d; exact d }
  inv :=
  { onShapes := fun t =>
      match t with
      | Sum.inl pb => (pb.1, Sum.inl pb.2)
      | Sum.inr pc => (pc.1, Sum.inr pc.2)
    onPos := by
      intro t
      cases t with
      | inl pb =>
          intro d; exact d
      | inr pc =>
          intro d; exact d }
  hom_inv_id := by
    apply Hom.ext
    · funext ps
      cases ps with
      | mk p s =>
        cases s <;> rfl
    · intro ps
      cases ps with
      | mk p s =>
        cases s <;> rfl
  inv_hom_id := by
    apply Hom.ext
    · funext t
      cases t <;> rfl
    · intro t
      cases t <;> rfl

end PolyC
