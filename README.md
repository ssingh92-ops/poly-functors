# Poly: Polynomial Functors as a Category in Lean 4

## Goal of the project

This repository develops a Lean 4 library for polynomial functors in the concrete **positions-and-directions** presentation, following the mathematical perspective of Nelson Niu and David Spivak’s *Polynomial Functors*. The goal is to formalize polynomial functors not as an isolated definition, but as a reusable category-theoretic library: objects, morphisms, semantics, algebraic constructions, bridges to existing Mathlib infrastructure, and universal-property style results.

The project begins from the container view of a polynomial functor, builds the category `PolyC` of polynomial functors and lens-style morphisms, and then develops increasingly rich structure on top of that core. The current milestone is an explicit equalizer construction together with the proof-engineering infrastructure needed to keep that construction stable in Lean.

## Main definitions

- **`PolyC`**  
  The central object of the library. A polynomial functor is represented by:
  - a type `A` of **positions**
  - a dependent family `B : A → Type` of **directions**  
  Intuitively, choosing a position determines which summand of the polynomial we are in, and the corresponding direction type describes the branching data attached to that position.

- **`PolyC.Hom`**  
  Morphisms between polynomial functors. A morphism `f : P ⟶ Q` is lens-style:
  - a forward map on positions
  - a backward pullback map on directions  
  This “forward on positions, backward on directions” asymmetry is one of the characteristic structural features of polynomial functors.

- **`eval`**  
  The type-level semantics of a polynomial functor:
  `P(X) = Σ a : A, (B a → X)`.  
  This interprets a polynomial as an endofunctor on types.

- **`evalFunctor` / semantic action on types**  
  The library packages the semantics of a polynomial functor as a functor in the variable `X`, and later files study how morphisms act on those semantics.

- **`sum`, `prod`, `composeObj`**  
  Explicit object-level constructions representing additive, multiplicative, and composition-style structure for polynomial functors.

- **Parallel / tensor-style structure**  
  The files `Parallel.lean` and `ParallelDistribute.lean` develop tensor-like structure and related distributivity behavior.

- **Composition-oriented structure**  
  The files `CompOnMorphisms.lean`, `CompSemantics.lean`, and `CompMonodial.lean` continue the composition story beyond the object level.

- **`toPFunctor` / `ofPFunctor`**  
  Bridge definitions connecting this project’s `PolyC` development to Mathlib’s existing `PFunctor` interface.

- **`EqObj`, `eq`, `IsEqualizer`, `eqLift`**  
  The current equalizer milestone. These definitions package the explicit equalizer object, the canonical map into the source polynomial functor, and a project-local universal-property interface.

## Main theorems and results

- **Category structure on `PolyC`**  
  The project defines identity and composition of morphisms and proves the category laws, so `PolyC` is a genuine category of polynomial functors and lens-style morphisms.

- **Functorial semantics**  
  The semantics of a polynomial functor is formalized as a functor on types, together with naturality-style compatibility results for morphisms.

- **Semantic equivalences for algebraic constructors**  
  The library proves explicit equivalences showing that the object-level constructions behave as expected semantically. In particular, the code develops equivalences for:
  - sums
  - products
  - composition-style object constructions

- **Bridge to Mathlib `PFunctor`**  
  The project proves compatibility results showing that the custom `PolyC` representation can be translated to and from Mathlib’s `PFunctor` interface.

- **Additional categorical structure beyond bare `PFunctor`**  
  One of the main contributions of the project is not merely reusing `PFunctor`, but building extra categorical structure around it: lens-style morphisms, semantic evaluation, algebraic constructors, composition-oriented modules, and universal-property files.

- **Equalizer construction (current milestone)**  
  The equalizer object is defined explicitly in the positions-and-directions language: equalizing positions by restriction and directions by quotient. The equalizer interface and universal-property framework are in place, and the hardest remaining proof obligations are localized in `Equalizers.lean`.

- **Proof-engineering insight for equalizers**  
  A major lesson of the project is that the equalizer quotient should depend only on the underlying position `a : P.A`, not on the full subtype witness showing that two morphisms agree at that position. This isolates the hardest dependent-transport issues instead of letting them spread through the whole development.

## Relation to Mathlib

Mathlib already contains the unbundled notion of `PFunctor`. This project is not replacing that interface. Instead, it builds a book-guided categorical layer on top of the positions-and-directions/container viewpoint and then connects back to Mathlib through `PFunctorBridge.lean`.

The main difference from what is already in Mathlib is therefore not “another polynomial datatype,” but rather the extra categorical structure developed around it: explicit morphisms, semantics, algebraic constructors, monoidal/composition-oriented modules, and the current universal-property milestone.

## References

- Nelson Niu and David Spivak, *Polynomial Functors*  
- Mathlib4, especially the existing `PFunctor` development  
- The container/lens perspective from functional programming, which this project connects to the category-theoretic language of polynomial functors

## Future work

The next achievable step is to finish the remaining localized equalizer proof obligations and turn the current equalizer scaffolding into a fully verified universal-property result. After that, the natural direction is to continue pushing the library toward more of the categorical structure emphasized in the textbook.

Natural future directions include:

- completing the equalizer milestone cleanly
- continuing to align all human-facing documentation and comments with the book’s **positions / directions** terminology
- packaging more limit- and colimit-style constructions explicitly
- strengthening the composition-oriented and monoidal parts of the library
- continuing to improve the bridge between this project and Mathlib’s `PFunctor`
- exploring whether a syntax-level DSL for polynomial expressions could support normalization or reflection-based proofs of categorical identities

## Build

```bash
lake update
lake build Poly
lake env lean Poly.lean
