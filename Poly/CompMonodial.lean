/-
Poly/CompMonoidal.lean

Finish Milestone 6 (monoidal structure from composition) by constructing:
- left unitor  : composeObj y P ≅ P
- right unitor : composeObj P y ≅ P
- associator   : composeObj (composeObj P Q) R ≅ composeObj P (composeObj Q R)

Lean note:
We DO NOT use the notation `▷` here, because multiple files may declare it.
That can create "Ambiguous term" errors even if both notations expand to the same definition.
So we write `composeObj` explicitly everywhere.
-/
import Poly.Parallel      -- provides PolyC.y
import Poly.Composition   -- provides composeObj

universe u
open CategoryTheory

namespace PolyC

/-- Left unitor for composition: y ▷ P ≅ P (written with composeObj). -/
def compLeftUnitor (P : PolyC.{u, u}) : composeObj (PolyC.y.{u, u}) P ≅ P where
  hom :=
    { onShapes := fun s => s.2 PUnit.unit
      onPos := fun s pb => ⟨PUnit.unit, pb⟩ }
  inv :=
    { onShapes := fun a => ⟨PUnit.unit, fun _ => a⟩
      onPos := fun a d => d.2 }
  hom_inv_id := by
    -- show: hom ≫ inv = 𝟙
    apply Hom.ext
    · funext s
      cases s with
      | mk u k =>
        cases u
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext t
          cases t
          rfl
    · intro s
      apply heq_of_eq
      funext d
      cases s with
      | mk u k =>
        cases u
        cases d with
        | mk t pb =>
          cases t
          rfl
  inv_hom_id := by
    -- show: inv ≫ hom = 𝟙
    apply Hom.ext
    · funext a
      rfl
    · intro a
      apply heq_of_eq
      funext pb
      rfl

/-- Right unitor for composition: P ▷ y ≅ P (written with composeObj). -/
def compRightUnitor (P : PolyC.{u, u}) : composeObj P (PolyC.y.{u, u}) ≅ P where
  hom :=
    { onShapes := fun s => s.1
      onPos := fun s pb => ⟨pb, PUnit.unit⟩ }
  inv :=
    { onShapes := fun a => ⟨a, fun _ => PUnit.unit⟩
      onPos := fun a d => d.1 }
  hom_inv_id := by
    apply Hom.ext
    · funext s
      cases s with
      | mk a k =>
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext p
          -- any value in PUnit is definitional after cases
          cases (k p)
          rfl
    · intro s
      apply heq_of_eq
      funext d
      cases s with
      | mk a k =>
        cases d with
        | mk pb uu =>
          cases uu
          rfl
  inv_hom_id := by
    apply Hom.ext
    · funext a
      rfl
    · intro a
      apply heq_of_eq
      funext pb
      rfl

/--
Associator for composition:
  (P ▷ Q) ▷ R ≅ P ▷ (Q ▷ R)
written with composeObj explicitly.
-/
def compAssociator (P Q R : PolyC.{u, u}) :
    composeObj (composeObj P Q) R ≅ composeObj P (composeObj Q R) where
  hom :=
    { onShapes := fun s =>
        let a : P.A := s.1.1
        let k : P.B a → Q.A := s.1.2
        let h : (Sigma (fun p : P.B a => Q.B (k p))) → R.A := s.2
        ⟨a, fun p => ⟨k p, fun q => h ⟨p, q⟩⟩⟩
      onPos := fun s d =>
        ⟨⟨d.1, d.2.1⟩, d.2.2⟩ }
  inv :=
    { onShapes := fun t =>
        let a : P.A := t.1
        let K : P.B a → (Sigma (fun b : Q.A => (Q.B b → R.A))) := t.2
        let k : P.B a → Q.A := fun p => (K p).1
        let h : (Sigma (fun p : P.B a => Q.B (k p))) → R.A :=
          fun pq => (K pq.1).2 pq.2
        ⟨⟨a, k⟩, h⟩
      onPos := fun t d =>
        ⟨d.1.1, ⟨d.1.2, d.2⟩⟩ }
  hom_inv_id := by
    apply Hom.ext
    · funext s
      cases s with
      | mk sPQ h =>
        cases sPQ with
        | mk a k =>
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            funext pq
            cases pq with
            | mk p q =>
              rfl
    · intro s
      apply heq_of_eq
      funext d
      cases d with
      | mk pq rpos =>
        cases pq with
        | mk p q =>
          rfl
  inv_hom_id := by
    apply Hom.ext
    · funext t
      cases t with
      | mk a K =>
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext p
          cases (K p) with
          | mk b hb =>
            rfl
    · intro t
      apply heq_of_eq
      funext d
      cases d with
      | mk p qr =>
        cases qr with
        | mk q rpos =>
          rfl

end PolyC
