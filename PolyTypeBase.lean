/-
# PolyTypeBase.lean — Polynomials-as-Containers (Set/Type-level Poly) for UW Math AI Lab

## What this file is
This file defines a small, concrete category of “polynomials” in the container sense:

  P ≔ (A, B)
  - A : Type of SHAPES (constructors / blueprints)
  - B : A → Type of POSITIONS/SLOTS for each shape

Reading rule:
- Choose a shape a : A, then there are |B a| slots to fill.

## Project intent
A computable representation of polynomial functors and their morphisms,
prior to the LCCC/slice-based development.

Type-level extension:
  P(X) = Σ (a : A), (B a → X)

Morphisms are container morphisms (lens-like polarity):
  f : P ⟶ Q
  f.onShapes : P.A → Q.A
  f.onPos    : ∀ a : P.A, Q.B (f.onShapes a) → P.B a

Interpretation:
- A source shape maps forward to a target shape.
- Target positions pull back to source positions.
- Pullback on positions enables contravariant transport of fillings.

Core deliverables:
  (1) Category structure on PolyC
  (2) Evaluation on types
  (3) Composition by substitution of slot maps
  (4) Sum/product/compose constructors matching pointwise functor operations

## What this file is NOT
- Not the LCCC/slice/Beck–Chevalley development.
- Not numerical ML/AD code.

## Conventions
- Name `PolyC` avoids clashing with Mathlib’s `Poly`.
- Universes: u (shapes), v (positions), w (input types X).
-/
import Mathlib
import Mathlib.Data.PFunctor.Univariate.Basic

universe u v w

open CategoryTheory

structure PolyC where
  A : Type u
  B : A → Type v

namespace PolyC

def eval (P : PolyC.{u, v}) (X : Type w) : Type (max u v w) :=
  Sigma (fun a : P.A => (P.B a → X))

structure Hom (P Q : PolyC.{u, v}) where
  onShapes : P.A → Q.A
  onPos    : ∀ a : P.A, Q.B (onShapes a) → P.B a

def id (P : PolyC.{u, v}) : Hom P P where
  onShapes := fun a => a
  onPos    := fun _ p => p

def comp {P Q R : PolyC.{u, v}} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  onShapes := fun a => g.onShapes (f.onShapes a)
  onPos := fun a rpos => f.onPos a (g.onPos (f.onShapes a) rpos)

def map {P Q : PolyC.{u, v}} (f : Hom P Q) {X : Type w} :
    P.eval X → Q.eval X
  | ⟨a, fillP⟩ =>
      ⟨f.onShapes a, fun qpos => fillP (f.onPos a qpos)⟩

@[ext (iff := false)]
lemma Hom.ext {P Q : PolyC.{u, v}} (f g : Hom P Q)
    (hShapes : f.onShapes = g.onShapes)
    (hPos : ∀ a : P.A, HEq (f.onPos a) (g.onPos a)) : f = g := by
  cases f with
  | mk fShapes fPos =>
    cases g with
    | mk gShapes gPos =>
      cases hShapes
      have : fPos = gPos := by
        funext a
        exact eq_of_heq (hPos a)
      cases this
      rfl

instance : Category PolyC.{u, v} where
  Hom P Q := Hom P Q
  id P := id P
  comp f g := comp f g
  id_comp := by
    intro X Y f
    rfl
  comp_id := by
    intro X Y f
    rfl
  assoc := by
    intro W X Y Z f g h
    rfl

/-
============================================================
Functor semantics (evaluation as a functor in X)
============================================================
-/

def evalMap (P : PolyC.{u, v}) {X Y : Type w} (h : X → Y) :
    P.eval X → P.eval Y
  | ⟨a, fill⟩ => ⟨a, fun p => h (fill p)⟩

def evalFunctor (P : PolyC.{u, v}) : Type w ⥤ Type (max u v w) where
  obj X := P.eval X
  map {X Y} h := evalMap P h
  map_id := by
    intro X
    funext x
    cases x
    rfl
  map_comp := by
    intro X Y Z f g
    funext x
    cases x
    rfl

theorem map_natural {P Q : PolyC.{u, v}} (f : Hom P Q) {X Y : Type w} (h : X → Y) :
    (evalMap Q h) ∘ (map f) = (map f) ∘ (evalMap P h) := by
  funext x
  cases x with
  | mk a fill => rfl

/-
============================================================
Sum and product of polynomials (verified algebra)
============================================================
-/

def sum (P Q : PolyC.{u, v}) : PolyC.{u, v} where
  A := Sum P.A Q.A
  B := fun s =>
    match s with
    | Sum.inl a => P.B a
    | Sum.inr b => Q.B b

def prod (P Q : PolyC.{u, v}) : PolyC.{u, v} where
  A := P.A × Q.A
  B := fun ab => Sum (P.B ab.1) (Q.B ab.2)

def evalSumEquiv (P Q : PolyC.{u, v}) (X : Type w) :
    (sum P Q).eval X ≃ Sum (P.eval X) (Q.eval X) where
  toFun
    | ⟨Sum.inl a, fill⟩ => Sum.inl ⟨a, fill⟩
    | ⟨Sum.inr b, fill⟩ => Sum.inr ⟨b, fill⟩
  invFun
    | Sum.inl ⟨a, fill⟩ => ⟨Sum.inl a, fill⟩
    | Sum.inr ⟨b, fill⟩ => ⟨Sum.inr b, fill⟩
  left_inv := by
    intro x
    cases x with
    | mk s fill =>
      cases s <;> rfl
  right_inv := by
    intro y
    cases y <;> rfl

def evalProdEquiv (P Q : PolyC.{u, v}) (X : Type w) :
    (prod P Q).eval X ≃ (P.eval X × Q.eval X) where
  toFun
    | ⟨⟨a, b⟩, fill⟩ =>
      (⟨a, fun pa => fill (Sum.inl pa)⟩, ⟨b, fun qb => fill (Sum.inr qb)⟩)
  invFun
    | (⟨a, fillA⟩, ⟨b, fillB⟩) =>
      ⟨⟨a, b⟩, fun s => Sum.casesOn s fillA fillB⟩
  left_inv := by
    intro x
    cases x with
    | mk ab fill =>
      cases ab with
      | mk a b =>
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          funext s
          cases s <;> rfl
  right_inv := by
    rintro ⟨⟨a, fillA⟩, ⟨b, fillB⟩⟩
    rfl

/-
============================================================
Polynomial substitution (object-level composition)
============================================================
-/

def composeObj (P Q : PolyC.{u, v}) : PolyC.{max u v, v} where
  A := Sigma (fun a : P.A => (P.B a → Q.A))
  B := fun s => Sigma (fun p : P.B s.1 => Q.B (s.2 p))

def evalComposeEquiv (P Q : PolyC.{u, v}) (X : Type w) :
    (composeObj P Q).eval X ≃ P.eval (Q.eval X) where
  toFun
    | ⟨⟨a, k⟩, fill⟩ =>
      ⟨a, fun p => ⟨k p, fun qpos => fill ⟨p, qpos⟩⟩⟩
  invFun
    | ⟨a, g⟩ =>
      ⟨⟨a, fun p => (g p).1⟩, fun pq => (g pq.1).2 pq.2⟩
  left_inv := by
    rintro ⟨⟨a, k⟩, fill⟩
    rfl

  right_inv := by
    rintro ⟨a, g⟩
    rfl

/-
============================================================
Translation to/from Mathlib PFunctor
============================================================
-/

def toPFunctor (P : PolyC.{u, v}) : PFunctor.{u, v} where
  A := P.A
  B := P.B

def ofPFunctor (P : PFunctor.{u, v}) : PolyC.{u, v} where
  A := P.A
  B := P.B

@[simp] lemma ofPFunctor_toPFunctor (P : PolyC.{u, v}) :
    ofPFunctor (toPFunctor P) = P := by
  cases P
  rfl

@[simp] lemma toPFunctor_ofPFunctor (P : PFunctor.{u, v}) :
    toPFunctor (ofPFunctor P) = P := by
  cases P
  rfl

/--
Explicit object-level evaluation for Mathlib `PFunctor` with no reliance on field names.
-/
def pfunctorObj (F : PFunctor.{u, v}) (X : Type w) : Type (max u v w) :=
  Sigma (fun a : F.A => (F.B a → X))

@[simp] lemma eval_eq_pfunctor_obj (P : PolyC.{u, v}) (X : Type w) :
    P.eval X = pfunctorObj (toPFunctor P) X := by
  rfl

/-
============================================================
Notes on Set vs Type modeling in Lean
============================================================

Lean implementation uses `Type` as the ambient category for computable semantics.
Textbook presentations often use `Set`.

Set-model duplication risk:
- In Lean, "Set" as a mathematical category is typically modeled either as:
  (i) `Type` with functions, interpreted as sets informally, or
  (ii) a bundled category of small types with extensional equality properties.
- The container construction `Σ a, (B a → X)` matches the textbook Set formula
  `∑_{a∈A} X^{B(a)}` when `X^{B(a)}` is read as functions `B(a) → X`.
- A separate Set-only version becomes syntactic duplication unless the development
  needs set-level quotients, classical choice principles, or proof-irrelevance
  properties not present/assumed in the Type-level core.
-/

end PolyC
