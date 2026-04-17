import Poly.Core

/-
============================================================
Poly/Equalizers.lean
============================================================

This file constructs equalizers in the category `PolyC` of polynomial
functors / containers.

If you are new to equalizers, here is the basic picture.

Given parallel arrows
  f g : P ⟶ Q
an equalizer is an object `E` together with a map
  e : E ⟶ P
such that

1. `e ≫ f = e ≫ g`, and
2. for any `h : R ⟶ P` satisfying `h ≫ f = h ≫ g`,
   there exists a unique `u : R ⟶ E` with `u ≫ e = h`.

In the positions-and-directions presentation of polynomial functors,
the textbook says that equalizers in `Poly` are computed by:
  • taking an equalizer on positions, and
  • taking a coequalizer on directions.

This file follows exactly that strategy.

Lean implementation note:
internally, the current core file still uses the earlier field names
`A`, `B`, `onShapes`, and `onPos`. In the mathematical interpretation:

  • `A` is the type of positions
  • `B a` is the type of directions at position `a`
  • `onShapes` is the forward map on positions
  • `onPos` is the backward pullback map on directions

The hardest proof-engineering issue is that the direction quotient
interacts with dependent equalities coming from the equalizer position
subtype. To keep those difficulties under control, this file first
packages the direction quotient as a small coequalizer-style API:

  • `dirMk`
  • `dirMk_eq`
  • `dirDesc`

and then uses those lemmas in the larger equalizer proofs.
-/

open CategoryTheory

namespace PolyC

universe u v

/-
==============================================================================
A helper for heterogeneous equality of functions across casts
==============================================================================

The equalizer equation compares two direction maps whose domains are only
propositionally equal, not definitionally equal. This helper says:

if
  h : α = β
and applying `F` to `x : α` always agrees with applying `G` to `cast h x`,
then `F` and `G` are heterogeneously equal as functions.
-/

/-- Function extensionality across a casted domain. -/
private lemma heqFunOfCast
    {α β γ : Type v}
    (h : α = β)
    (F : α → γ)
    (G : β → γ)
    (H : ∀ x : α, F x = G (cast h x)) :
    HEq F G := by
  cases h
  exact heq_of_eq (funext H)

/-
==============================================================================
Transport of directions along equalities of positions
==============================================================================

If two positions are equal, a direction over one position can be
transported to a direction over the other.
-/

/-- Transport a direction along an equality of positions. -/
def castQPos {Q : PolyC.{u, v}} {x y : Q.A} (h : x = y) : Q.B x → Q.B y := by
  intro q
  cases h
  exact q

/--
`castQPos` produces a heterogeneously equal direction.

This is the transport fact that lets us compare the two pullback maps
on directions without repeatedly destructing equalities inside the big
equalizer proofs.
-/
lemma castQPos_heq {Q : PolyC.{u, v}} {x y : Q.A}
    (h : x = y) (q : Q.B x) :
    HEq q (castQPos (Q := Q) h q) := by
  cases h
  rfl

/--
`castQPos` agrees with Lean's raw `cast` expression.

This is useful because some goals are generated in terms of
`cast (congrArg Q.B h) q` rather than the helper `castQPos h q`.
-/
lemma castQPos_eq_cast {Q : PolyC.{u, v}} {x y : Q.A}
    (h : x = y) (q : Q.B x) :
    castQPos (Q := Q) h q = cast (congrArg Q.B h) q := by
  cases h
  rfl

/-
==============================================================================
A lightweight equalizer predicate
==============================================================================

We use a project-local universal-property structure instead of importing
the full Mathlib limits API. This keeps the current development small and
focused.
-/

/--
`IsEqualizer f g e` says that `e : E ⟶ P` is an equalizer of the
parallel pair `f g : P ⟶ Q`.
-/
structure IsEqualizer {P Q E : PolyC.{u, v}}
    (f g : P ⟶ Q) (e : E ⟶ P) : Prop where
  condition : e ≫ f = e ≫ g
  lift :
    ∀ {R : PolyC.{u, v}} (h : R ⟶ P),
      h ≫ f = h ≫ g →
      ∃! u : R ⟶ E, u ≫ e = h

section EqualizerConstruction

variable {P Q : PolyC.{u, v}} (f g : P ⟶ Q)

/-
==============================================================================
Step 1: Positions of the equalizer
==============================================================================

The equalizer positions are exactly the positions of `P` where the two
position maps agree.
-/

/-- Positions of the equalizer object. -/
abbrev EqA : Type u :=
  { a : P.A // f.onShapes a = g.onShapes a }

/-
==============================================================================
Step 2: Directions of the equalizer
==============================================================================

At an equalizer position `a`, the directions are obtained by quotienting
the original directions `P.B a` by the equivalence relation generated by
identifying the two pullbacks of a common target direction.

This is the "coequalizer on directions" part of the textbook construction.

Important proof-engineering choice:
the quotient depends only on the underlying position `a : P.A`, not on the
full subtype witness `⟨a, proof⟩`. This avoids dragging proof objects into
later type-level transports.
-/

/--
Generating relation on directions over a fixed underlying position `a : P.A`.

Two directions are related if they arise by pulling back heterogeneously equal
target directions along `f` and `g`.
-/
def EqBaseRelOn (a : P.A) : P.B a → P.B a → Prop :=
  fun x y =>
    ∃ qf : Q.B (f.onShapes a),
      ∃ qg : Q.B (g.onShapes a),
        x = f.onPos a qf ∧
        y = g.onPos a qg ∧
        HEq qf qg

/-- Equivalence closure of the generating relation. -/
abbrev EqRelOn (a : P.A) : P.B a → P.B a → Prop :=
  Relation.EqvGen (EqBaseRelOn (f := f) (g := g) a)

/-- Setoid generated by `EqRelOn`. -/
def EqSetoidOn (a : P.A) : Setoid (P.B a) where
  r := EqRelOn (f := f) (g := g) a
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x
      exact Relation.EqvGen.refl x
    · intro x y hxy
      exact Relation.EqvGen.symm x y hxy
    · intro x y z hxy hyz
      exact Relation.EqvGen.trans x y z hxy hyz

/--
Direction type at an equalizer position.

This quotient depends only on the underlying position `a.1`.
-/
abbrev EqB (a : EqA (f := f) (g := g)) : Type v :=
  Quot (EqSetoidOn (f := f) (g := g) a.1)

/-
==============================================================================
Step 3: Direction quotient API
==============================================================================

These lemmas are the reusable "coequalizer-style" interface for the quotient.

The point is to avoid repeatedly writing raw `Quot.sound`, `Quot.lift`,
and `Quot.inductionOn` directly in the main proofs.
-/

/-- The quotient map sending a direction to its class. -/
def dirMk (a : EqA (f := f) (g := g)) :
    P.B a.1 → EqB (f := f) (g := g) a :=
  Quot.mk _

/--
A single basic equalizing step belongs to the generated relation.

This is the relation-level fact saying that two directions coming from
the same target direction become identified.
-/
lemma eqRel_step (a : EqA (f := f) (g := g))
    (q : Q.B (f.onShapes a.1)) :
    EqRelOn (f := f) (g := g) a.1
      (f.onPos a.1 q)
      (g.onPos a.1 (castQPos (Q := Q) a.2 q)) := by
  refine Relation.EqvGen.rel
    (r := EqBaseRelOn (f := f) (g := g) a.1)
    (x := f.onPos a.1 q)
    (y := g.onPos a.1 (castQPos (Q := Q) a.2 q))
    ?_
  exact ⟨q, castQPos (Q := Q) a.2 q, rfl, rfl, castQPos_heq (Q := Q) a.2 q⟩

/--
The basic quotient equality for directions.

After applying the quotient map `dirMk`, the two pullback directions
become equal.
-/
lemma dirMk_eq (a : EqA (f := f) (g := g))
    (q : Q.B (f.onShapes a.1)) :
    dirMk (f := f) (g := g) a (f.onPos a.1 q)
      =
    dirMk (f := f) (g := g) a
      (g.onPos a.1 (castQPos (Q := Q) a.2 q)) := by
  apply Quot.sound
  exact eqRel_step (f := f) (g := g) a q

/--
Eliminator for the direction quotient.

To define a function out of the quotient direction type, it is enough
to define a function on representatives and prove that it respects the
generating relation.
-/
def dirDesc
    (a : EqA (f := f) (g := g))
    {β : Type v}
    (k : P.B a.1 → β)
    (hk :
      ∀ qf : Q.B (f.onShapes a.1),
      ∀ qg : Q.B (g.onShapes a.1),
        HEq qf qg →
        k (f.onPos a.1 qf) = k (g.onPos a.1 qg)) :
    EqB (f := f) (g := g) a → β := by
  refine Quot.lift k ?_
  intro x y hxy
  induction hxy with
  | refl x =>
      rfl
  | rel x y hbase =>
      rcases hbase with ⟨qf, qg, hx, hy, hq⟩
      subst hx
      subst hy
      exact hk qf qg hq
  | symm x y hxy ih =>
      exact ih.symm
  | trans x y z hxy hyz ihxy ihyz =>
      exact Eq.trans ihxy ihyz

/-
==============================================================================
Step 4: The equalizer object
==============================================================================

The equalizer object combines:
  • the position subtype `EqA`
  • the direction quotient `EqB`
-/

/-- The equalizer object as a polynomial/container. -/
def EqObj : PolyC.{u, v} where
  A := EqA (f := f) (g := g)
  B := EqB (f := f) (g := g)

/-
==============================================================================
Step 5: The canonical map into P
==============================================================================

The canonical equalizer map:
  • forgets the proof on positions
  • sends each direction to its quotient class
-/

/-- The canonical equalizer map into `P`. -/
def eq : EqObj (f := f) (g := g) ⟶ P where
  onShapes := fun a => a.1
  onPos := fun a => dirMk (f := f) (g := g) a

/-
==============================================================================
Step 6: The equalizer equation
==============================================================================

We now show:
  eq ≫ f = eq ≫ g

Conceptually:
  • on positions: the two composites agree by the proof stored in `EqA`
  • on directions: the two composites agree by the quotient equation `dirMk_eq`

The main proof-engineering trick is `heqFunOfCast`, because the two
direction maps have propositionally equal domains rather than
definitionally equal domains.
-/

/-- The equalizing equation `eq ≫ f = eq ≫ g`. -/
theorem eq_comp_eq :
    (eq (f := f) (g := g)) ≫ f
      =
    (eq (f := f) (g := g)) ≫ g := by
  refine PolyC.Hom.ext
    ((eq (f := f) (g := g)) ≫ f)
    ((eq (f := f) (g := g)) ≫ g)
    ?hShapes ?hDirs
  · funext a
    exact a.2
  · intro a
    exact heqFunOfCast
      (h := congrArg Q.B a.2)
      ((eq (f := f) (g := g) ≫ f).onPos a)
      ((eq (f := f) (g := g) ≫ g).onPos a)
      (by
        intro q
        change
          dirMk (f := f) (g := g) a (f.onPos a.1 q)
            =
          dirMk (f := f) (g := g) a
            (g.onPos a.1 (cast (congrArg Q.B a.2) q))
        rw [← castQPos_eq_cast (Q := Q) a.2 q]
        exact dirMk_eq (f := f) (g := g) a q)

/-
==============================================================================
Step 7: A helper for the universal lift
==============================================================================

The main delicate step in constructing `eqLift` is proving that the
direction map `h.onPos r` respects the quotient relation.

The mistake in the earlier version was to destruct `heq` too late,
after defining data that already depended on it. So we isolate the needed
compatibility in a separate lemma *before* building the lift.
-/

/--
Congruence for the dependent `onPos` field of a morphism.

If two morphisms `F G : R ⟶ S` are equal, then their direction-pullback
functions agree. Since the domain of `F.onPos r` is
`S.B (F.onShapes r)` and the domain of `G.onPos r` is
`S.B (G.onShapes r)`, the two input directions may live in propositionally
different fibers. Therefore we assume the two input directions are
heterogeneously equal.

This lemma is deliberately stated for arbitrary variables `F` and `G`,
rather than for composite expressions such as `h ≫ f` and `h ≫ g`.
That makes equality elimination stable.
-/
private lemma hom_onPos_congr
    {R S : PolyC.{u, v}}
    {F G : R ⟶ S}
    (hFG : F = G)
    (r : R.A)
    (qF : S.B (F.onShapes r))
    (qG : S.B (G.onShapes r))
    (hq : HEq qF qG) :
    F.onPos r qF = G.onPos r qG := by
  revert qF qG hq
  cases hFG
  intro qF qG hq
  cases hq
  rfl

/--
If `h : R ⟶ P` equalizes `f` and `g`, then the induced pullback maps on
directions agree after transport.

This is the compatibility needed to descend `h.onPos r` through the
direction quotient.

The proof does NOT destruct `heq` directly. Instead, it applies the generic
congruence lemma `hom_onPos_congr` to the two composite morphisms
`h ≫ f` and `h ≫ g`.
-/
private lemma eqLift_respect_comp
    {R : PolyC.{u, v}}
    (h : R ⟶ P)
    (heq : h ≫ f = h ≫ g)
    (r : R.A)
    (qf : Q.B ((h ≫ f).onShapes r))
    (qg : Q.B ((h ≫ g).onShapes r))
    (hq : HEq qf qg) :
    (h ≫ f).onPos r qf = (h ≫ g).onPos r qg := by
  exact
    hom_onPos_congr
      (F := h ≫ f)
      (G := h ≫ g)
      heq r qf qg hq
/-
==============================================================================
Step 8: The universal lift
==============================================================================

Given `h : R ⟶ P` with `h ≫ f = h ≫ g`, define the induced map
`eqLift h heq : R ⟶ EqObj f g`.

Positions:
  send `r` to `h.onShapes r`, together with the proof that
  `f` and `g` agree after composing with `h`.

Directions:
  descend `h.onPos r` through the quotient using `dirDesc`.
-/

/-- The induced map into the equalizer from an equalizing arrow. -/
def eqLift {R : PolyC.{u, v}}
    (h : R ⟶ P)
    (heq : h ≫ f = h ≫ g) :
    R ⟶ EqObj (f := f) (g := g) := by
  let s : R.A → EqA (f := f) (g := g) := fun r =>
    ⟨h.onShapes r,
      by
        have hsFun : (h ≫ f).onShapes = (h ≫ g).onShapes :=
          congrArg (fun k => k.onShapes) heq
        have hs : (h ≫ f).onShapes r = (h ≫ g).onShapes r :=
          congrArg (fun fn => fn r) hsFun
        simpa [PolyC.comp] using hs⟩
  refine
    { onShapes := s
      onPos := ?_ }
  intro r
  refine dirDesc (f := f) (g := g) (s r)
    (k := fun p : P.B (h.onShapes r) => h.onPos r p)
    ?respect
  intro qf qg hq
  have hComp :
      (h ≫ f).onPos r qf = (h ≫ g).onPos r qg :=
    eqLift_respect_comp (f := f) (g := g) h heq r qf qg hq
  simpa [PolyC.comp] using hComp

/-
==============================================================================
Step 9: Universal property
==============================================================================

The existence part is given by `eqLift`.

The factorization proof is straightforward by extensionality.

For uniqueness, the key idea is:
  • do not build a separate equality of subtype-valued shape maps and then try
    to rewrite dependent direction domains along it;
  • instead, use the factorization equation `hu : u ≫ eq = h` directly;
  • after rewriting by `hu`, the comparison becomes computational.

That avoids the dependent-elimination failures that arose in the earlier
versions of the proof.
-/

/-- `EqObj f g` with `eq` satisfies the equalizer universal property. -/
theorem eqObj_isEqualizer :
    IsEqualizer (f := f) (g := g) (eq (f := f) (g := g)) := by
  refine ⟨eq_comp_eq (f := f) (g := g), ?_⟩
  intro R h heq
  refine ⟨eqLift (f := f) (g := g) (R := R) h heq, ?factorization, ?uniqueness⟩
  · -- Factorization: `(eqLift h heq) ≫ eq = h`.
    refine PolyC.Hom.ext
      ((eqLift (f := f) (g := g) (R := R) h heq) ≫ (eq (f := f) (g := g)))
      h
      ?hShapes ?hDirs
    · funext r
      rfl
    · intro r
      refine heq_of_eq ?_
      funext p
      rfl
  · -- Uniqueness: any other map factoring through `eq` must equal `eqLift`.
    intro u hu
    cases hu
    apply PolyC.Hom.ext
    · -- Positions:
      funext r
      apply Subtype.ext
      rfl
    · -- Directions:
      intro r
      apply heq_of_eq
      funext q
      refine Quot.inductionOn q ?_
      intro p
      rfl

end EqualizerConstruction

end PolyC
