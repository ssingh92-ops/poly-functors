import Poly.SmallColimits

/-
============================================================
Poly Project
File: Poly/Examples.lean
============================================================

This file gives small named polynomial functors and sanity checks for the
first-pass `PolyC` development.

The examples serve four roles:

1. They give readable examples for the README and final writeup.
2. They sanity-check the semantic interpretation

     P.eval X = Σ a : P.A, (P.B a → X).

3. They illustrate the positions-and-directions terminology used throughout
   the project.
4. They provide small test objects for products, coproducts, equalizers,
   pullbacks, coequalizers, and indexed constructions.

Terminology note:
the core code still uses the field names

  • `A`        = positions,
  • `B a`      = directions at position `a`,
  • `onShapes` = forward map on positions,
  • `onPos`    = backward pullback map on directions.

The comments below use positions/directions.
============================================================
-/

open CategoryTheory

namespace PolyC.Examples

universe u v w

/-
==============================================================================
Basic polynomial functors
==============================================================================
-/

/--
The variable polynomial `y`.

It has one position and one direction at that position. Semantically,

  y(X) = Σ _ : PUnit, (PUnit → X) ≃ X.
-/
def y : PolyC.{0, 0} where
  A := PUnit
  B := fun _ => PUnit

/--
The constant polynomial `K A`.

It has positions `A` and no directions at any position. Semantically,

  (K A)(X) = Σ a : A, (PEmpty → X) ≃ A.

We use `PEmpty` rather than `Empty` so that the no-direction type can live in
any direction universe.
-/
def K (A : Type u) : PolyC.{u, v} where
  A := A
  B := fun _ => PEmpty

/-- The zero polynomial, the constant polynomial at `Empty`. -/
def zero : PolyC.{0, 0} :=
  K.{0, 0} Empty

/-- The one polynomial, the constant polynomial at `PUnit`. -/
def one : PolyC.{0, 0} :=
  K.{0, 0} PUnit

/-- The constant-two polynomial. -/
def two : PolyC.{0, 0} :=
  K.{0, 0} Bool

/--
A pure power / representable polynomial `y^D`.

It has one position and directions `D`. Semantically,

  (y^D)(X) ≃ D → X.
-/
def Reader (D : Type v) : PolyC.{0, v} where
  A := PUnit
  B := fun _ => D

/--
A linear polynomial `A y`.

It has positions `A` and one direction at each position. Semantically,

  (A y)(X) ≃ A × X.
-/
def Linear (A : Type u) : PolyC.{u, 0} where
  A := A
  B := fun _ => PUnit

/--
A monomial polynomial `A y^D`.

It has positions `A` and the same direction type `D` at every position.
Semantically,

  (A y^D)(X) ≃ A × (D → X).
-/
def Monomial (A : Type u) (D : Type v) : PolyC.{u, v} where
  A := A
  B := fun _ => D

/--
The polynomial `y²`.

We use `Bool` as a two-element direction type, so evaluation gives two
independent elements of `X`.
-/
def PairPoly : PolyC.{0, 0} where
  A := PUnit
  B := fun _ => Bool

/--
The polynomial `1 + y`.

The `false` position has no directions, contributing a constant `1`.
The `true` position has one direction, contributing `y`.

Semantically, this evaluates to `Option X`.
-/
def MaybePoly : PolyC.{0, 0} where
  A := Bool
  B := fun b =>
    match b with
    | false => Empty
    | true => PUnit

/--
A list-like polynomial

  X ↦ Σ n : Nat, (Fin n → X).

This is the polynomial of length-indexed tuples. It is useful as a running
example because positions are lengths and directions are slots in that length.
-/
def ListPoly : PolyC.{0, 0} where
  A := Nat
  B := fun n => Fin n

/-
==============================================================================
Semantic normal forms
==============================================================================
-/

/-- Evaluation of `y` is equivalent to the input type. -/
def evalYEquiv (X : Type w) :
    y.eval X ≃ X where
  toFun z := z.2 PUnit.unit
  invFun x := ⟨PUnit.unit, fun _ => x⟩
  left_inv := by
    intro z
    rcases z with ⟨pos, fill⟩
    cases pos
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext p
      cases p
      rfl
  right_inv := by
    intro x
    rfl

/-- Evaluation of a constant polynomial is equivalent to its value type. -/
def evalKEquiv (A : Type u) (X : Type w) :
    ((K.{u, v} A).eval X) ≃ A where
  toFun z := z.1
  invFun a :=
    ⟨a,
      by
        intro e
        cases e⟩
  left_inv := by
    intro z
    rcases z with ⟨a, fill⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext e
      cases e
  right_inv := by
    intro a
    rfl

/-- Evaluation of the zero polynomial is empty. -/
def evalZeroEquiv (X : Type w) :
    zero.eval X ≃ Empty := by
  change (K.{0, 0} Empty).eval X ≃ Empty
  exact evalKEquiv Empty X

/-- Evaluation of the one polynomial is a singleton. -/
def evalOneEquiv (X : Type w) :
    one.eval X ≃ PUnit := by
  change (K.{0, 0} PUnit).eval X ≃ PUnit
  exact evalKEquiv PUnit X

/-- Evaluation of `y^D` is equivalent to the function type `D → X`. -/
def evalReaderEquiv (D : Type v) (X : Type w) :
    (Reader D).eval X ≃ (D → X) where
  toFun z := z.2
  invFun f := ⟨PUnit.unit, f⟩
  left_inv := by
    intro z
    rcases z with ⟨pos, fill⟩
    cases pos
    rfl
  right_inv := by
    intro f
    rfl

/-- Evaluation of `A y` is equivalent to `A × X`. -/
def evalLinearEquiv (A : Type u) (X : Type w) :
    (Linear A).eval X ≃ (A × X) where
  toFun z := (z.1, z.2 PUnit.unit)
  invFun ax := ⟨ax.1, fun _ => ax.2⟩
  left_inv := by
    intro z
    rcases z with ⟨a, fill⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext p
      cases p
      rfl
  right_inv := by
    intro ax
    cases ax
    rfl

/-- Evaluation of `A y^D` is equivalent to `A × (D → X)`. -/
def evalMonomialEquiv (A : Type u) (D : Type v) (X : Type w) :
    (Monomial A D).eval X ≃ (A × (D → X)) where
  toFun z := (z.1, z.2)
  invFun af := ⟨af.1, af.2⟩
  left_inv := by
    intro z
    rcases z with ⟨a, fill⟩
    rfl
  right_inv := by
    intro af
    cases af
    rfl

/-- Evaluation of `y²` is equivalent to `X × X`. -/
def evalPairEquiv (X : Type w) :
    PairPoly.eval X ≃ (X × X) where
  toFun z := (z.2 false, z.2 true)
  invFun xy :=
    ⟨PUnit.unit,
      fun b =>
        match b with
        | false => xy.1
        | true => xy.2⟩
  left_inv := by
    intro z
    rcases z with ⟨pos, fill⟩
    cases pos
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext b
      cases b <;> rfl
  right_inv := by
    intro xy
    cases xy
    rfl

/-- Evaluation of `1 + y` is equivalent to `Option X`. -/
def evalMaybeEquiv (X : Type w) :
    MaybePoly.eval X ≃ Option X where
  toFun := by
    intro z
    rcases z with ⟨b, fill⟩
    cases b
    · exact none
    · exact some (fill PUnit.unit)
  invFun := by
    intro ox
    cases ox with
    | none =>
        exact
          ⟨false,
            by
              intro e
              cases e⟩
    | some x =>
        exact ⟨true, fun _ => x⟩
  left_inv := by
    intro z
    rcases z with ⟨b, fill⟩
    cases b
    · apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext e
        cases e
    · apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext p
        cases p
        rfl
  right_inv := by
    intro ox
    cases ox <;> rfl

/-- The list-like polynomial evaluates definitionally as length-indexed tuples. -/
def evalListPolyEquiv (X : Type w) :
    ListPoly.eval X ≃ Sigma (fun n : Nat => Fin n → X) :=
  Equiv.refl _

/-
==============================================================================
Small lenses between examples
==============================================================================

These examples illustrate the lens convention:

  • positions move forward;
  • directions are pulled backward.
-/

/-- A function between constants induces a lens between constant polynomials. -/
def constMap {A B : Type u} (h : A → B) :
    (K.{u, v} A) ⟶ (K.{u, v} B) where
  onShapes := h
  onPos := by
    intro _ e
    cases e

/--
A function `B → A` induces a lens `y^A ⟶ y^B`.

This is contravariant in the direction type, as expected for representables.
-/
def readerMap {A B : Type v} (h : B → A) :
    Reader A ⟶ Reader B where
  onShapes := fun _ => PUnit.unit
  onPos := fun _ b => h b

/-- A function between position types induces a lens between linear polynomials. -/
def linearMap {A B : Type u} (h : A → B) :
    Linear A ⟶ Linear B where
  onShapes := h
  onPos := fun _ _ => PUnit.unit

/-- A position map and a direction pullback give a lens between monomials. -/
def monomialMap {A B : Type u} {D E : Type v}
    (hA : A → B) (hD : E → D) :
    Monomial A D ⟶ Monomial B E where
  onShapes := hA
  onPos := fun _ e => hD e

/-- The unique lens from `y` to the terminal constant polynomial `1`. -/
def yToOne : y ⟶ one where
  onShapes := fun _ => PUnit.unit
  onPos := by
    intro _ e
    cases e

/-- The inclusion of the `y` summand into `1 + y`. -/
def yIntoMaybe : y ⟶ MaybePoly where
  onShapes := fun _ => true
  onPos := fun _ _ => PUnit.unit

/-- The inclusion of the `1` summand into `1 + y`. -/
def oneIntoMaybe : one ⟶ MaybePoly where
  onShapes := fun _ => false
  onPos := by
    intro _ e
    cases e

/-- Collapse `1 + y` to the terminal constant polynomial. -/
def maybeToOne : MaybePoly ⟶ one where
  onShapes := fun _ => PUnit.unit
  onPos := by
    intro _ e
    cases e

/-- Swap the two directions of `y²`. -/
def pairSwap : PairPoly ⟶ PairPoly where
  onShapes := fun _ => PUnit.unit
  onPos := fun _ b => not b

/-
==============================================================================
Products, pullbacks, equalizers, and coequalizers
==============================================================================
-/

/-- The binary product `y × y`. -/
def yProductY : PolyC.{0, 0} :=
  finiteProduct y y

/-- The pullback of `y → 1 ← y`. -/
def yPullbackOverOne : PolyC.{0, 0} :=
  finitePullback yToOne yToOne

/-- The equalizer of the identity pair on `y`. -/
def yIdEqualizer : PolyC.{0, 0} :=
  finiteEqualizer
    (P := y)
    (Q := y)
    (𝟙 y)
    (𝟙 y)

/-- The coequalizer of the identity pair on `y`. -/
def yIdCoequalizer : PolyC.{0, 0} :=
  smallCoequalizer
    (P := y)
    (Q := y)
    (𝟙 y)
    (𝟙 y)

/-- The product example satisfies the product universal property. -/
def yProductYHomEquiv (R : PolyC.{0, 0}) :
    (R ⟶ yProductY) ≃ (R ⟶ y) × (R ⟶ y) :=
  finiteProductHomEquiv R y y

/-- The pullback example satisfies the pullback universal property. -/
theorem yPullbackOverOne_isPullback :
    IsPullback
      yToOne
      yToOne
      (finitePullbackFst yToOne yToOne)
      (finitePullbackSnd yToOne yToOne) := by
  exact finitePullback_isPullback yToOne yToOne

/-- The identity equalizer example satisfies the equalizer universal property. -/
theorem yIdEqualizer_isEqualizer :
    IsEqualizer
      (𝟙 y)
      (𝟙 y)
      (finiteEqualizerMap
        (P := y)
        (Q := y)
        (𝟙 y)
        (𝟙 y)) := by
  exact finiteEqualizer_isEqualizer
    (P := y)
    (Q := y)
    (𝟙 y)
    (𝟙 y)

/-- The identity coequalizer example satisfies the coequalizer universal property. -/
theorem yIdCoequalizer_isCoequalizer :
    IsCoequalizer
      (𝟙 y)
      (𝟙 y)
      (smallCoequalizerMap
        (P := y)
        (Q := y)
        (𝟙 y)
        (𝟙 y)) := by
  exact smallCoequalizer_isCoequalizer
    (P := y)
    (Q := y)
    (𝟙 y)
    (𝟙 y)

/-
==============================================================================
Indexed product and indexed coproduct examples
==============================================================================
-/

/--
A small Bool-indexed family.

The `false` component is `1`, and the `true` component is `y`.
-/
def BoolFamily : Bool → PolyC.{0, 0}
  | false => one
  | true => y

/-- The indexed product of the Bool-indexed family. -/
def boolIndexedProduct : PolyC.{0, 0} :=
  finiteIndexedProduct BoolFamily

/-- The indexed coproduct of the Bool-indexed family. -/
def boolIndexedCoproduct : PolyC.{0, 0} :=
  smallIndexedCoproduct BoolFamily

/-- The Bool-indexed product satisfies its universal property. -/
theorem boolIndexedProduct_isIndexedProduct :
    IsIndexedProduct
      BoolFamily
      boolIndexedProduct
      (finiteIndexedProductProj BoolFamily) := by
  exact finiteIndexedProduct_isIndexedProduct BoolFamily

/-- The Bool-indexed coproduct satisfies its universal property. -/
theorem boolIndexedCoproduct_isIndexedCoproduct :
    IsIndexedCoproduct
      BoolFamily
      boolIndexedCoproduct
      (smallIndexedCoproductIn BoolFamily) := by
  exact smallIndexedCoproduct_isIndexedCoproduct BoolFamily

/-- Evaluation of the Bool-indexed product is a product of evaluations. -/
def evalBoolIndexedProductEquiv (X : Type w) :
    boolIndexedProduct.eval X ≃ (∀ b : Bool, (BoolFamily b).eval X) :=
  finiteIndexedProductEvalEquiv BoolFamily X

/-- Evaluation of the Bool-indexed coproduct is a coproduct of evaluations. -/
def evalBoolIndexedCoproductEquiv (X : Type w) :
    boolIndexedCoproduct.eval X ≃ Sigma (fun b : Bool => (BoolFamily b).eval X) :=
  smallIndexedCoproductEvalEquiv BoolFamily X

/-
==============================================================================
First-pass milestone sanity checks
==============================================================================

These are small public-facing checks that the main first-pass packages are
available from this examples file.
-/

/-- The project-local small-limits ingredients are available. -/
theorem examples_smallLimitsAvailable :
    SmallLimitIngredients.{0, 0} := by
  exact smallLimitIngredients_done

/-- The project-local small-colimits ingredients are available. -/
theorem examples_smallColimitsAvailable :
    SmallColimitIngredients.{0, 0} := by
  exact smallColimitIngredients_done

/-- The positions-and-directions theorem family is available. -/
theorem examples_positionsDirectionsAvailable :
    PositionsDirectionsEvidence.{0, 0} := by
  exact positionsDirectionsEvidence_done

end PolyC.Examples
