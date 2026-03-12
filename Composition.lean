/-
============================================================
EE598 — Poly Project
File: Poly/Composition.lean
============================================================

## Purpose
Define the “substitution / composition” of container polynomials.

Intuition:
- P has shapes a and positions p : P.B a
- Q has shapes b and positions q : Q.B b

To build the composite P ∘ Q:
- choose a shape a of P
- for each position p of that shape, choose a Q-shape k(p)
So a *composite shape* is:
  (a, k) where k : P.B a → Q.A

Then a *composite position* must specify:
- which outer position p you are in
- which inner position q you are in (inside Q at shape k(p))

So positions are:
  (p, q) where p : P.B a and q : Q.B (k p)

This is exactly the container substitution formula.

## What we prove
We prove:
  (P ∘ Q)(X) ≃ P(Q(X))
as an explicit equivalence of types.

============================================================
-/
import Poly.Core

universe u v w

namespace PolyC

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

end PolyC
