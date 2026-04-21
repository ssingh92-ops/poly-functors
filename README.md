# Poly: Polynomial Functors as a Category in Lean 4

## Goal of the project

This repository develops a Lean 4 library for polynomial functors in the concrete **positions-and-directions** presentation, following Nelson Niu and David Spivak’s *Polynomial Functors*. The goal is not only to define polynomial functors as container-style data, but to formalize the **category of polynomial functors** itself: its objects, morphisms, semantics, algebraic operations, universal constructions, and the first layer of structure needed for the later composition-product and comonoid story in the book.

The project begins from the container interpretation of a polynomial functor and builds a concrete category `PolyC` of polynomial functors and dependent-lens-style morphisms. On top of that core it develops:

- semantic evaluation as type-level endofunctors,
- sums, products, indexed products, and indexed coproducts,
- equalizers, pullbacks, and coequalizers,
- small-limits and small-colimits packaging,
- a positions-and-directions theorem family collecting the book’s concrete formulas,
- the Chapter 6 composition product,
- semantic substitution for the composition product,
- and a first layer of interaction theorems for the composition product.

Although the book usually works over `Set`, this repository formalizes the same mathematics over Lean universes `Type u`. This should not be read as a different mathematical theory. In Lean, `Type` plays the role of a universe of small sets together with the dependent type structure needed for the positions-and-directions presentation. So the implementation is best understood as a **Type-level realization of the book’s Set-level formulas**, rather than as a departure from them.

## What the project adds beyond Mathlib

Mathlib already contains two important ingredients:

1. generic polynomial/container infrastructure such as `PFunctor`, and  
2. abstract category-theory machinery for limits, colimits, pullbacks, equalizers, monoidal categories, and related notions.

This project is therefore **not** trying to replace Mathlib’s abstract framework. What it adds is the **concrete, book-guided middle layer**:

- a named category `PolyC` of polynomial functors in the positions-and-directions presentation,
- explicit dependent-lens-style morphisms,
- explicit semantic evaluation,
- explicit object-level constructions,
- explicit universal-property constructions,
- explicit positions/directions formulas,
- and a concrete path back to Mathlib’s existing `PFunctor` infrastructure.

So the main contribution is not “another polynomial datatype,” but rather a **book-faithful categorical library** around polynomial functors.

## Main definitions

### `PolyC`

The central object of the library. A polynomial functor is represented by:

- a type `A` of **positions**
- a dependent family `B : A → Type` of **directions**

Semantically, a polynomial functor is interpreted by

```lean
P.eval X = Σ a : P.A, (P.B a → X)
