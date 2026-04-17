# Poly: Polynomial Functors as a Category in Lean 4

## Goal of the project

This repository develops a Lean 4 library for polynomial functors in the concrete **positions-and-directions** presentation, following the mathematical perspective of Nelson Niu and David Spivak’s *Polynomial Functors*. The goal is to formalize polynomial functors not as an isolated definition, but as a reusable category-theoretic library: objects, morphisms, semantics, algebraic constructions, bridges to existing Mathlib infrastructure, and universal-property style results.

The project begins from the container view of a polynomial functor, builds the category `PolyC` of polynomial functors and lens-style morphisms, and then develops increasingly rich structure on top of that core. The current milestone is an explicit equalizer construction together with the proof-engineering infrastructure needed to keep that construction stable in Lean.

Although the book usually presents polynomial functors over `Set`, this repository formalizes the same constructions over Lean universes `Type u`. This should not be read as a different mathematical theory. In Lean, `Type` plays the role of a universe of small sets together with the dependent type structure needed for the positions-and-directions presentation. So the implementation is best understood as a Type-level realization of the book’s Set-level formulas, rather than as a departure from them.

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

- **Equalizer construction**  
  The project now includes an explicit equalizer construction for parallel morphisms `f g : P ⟶ Q`. Following the book’s Chapter 5 pattern, the equalizer is computed by restricting positions and quotienting directions: positions are kept exactly where the two position maps agree, and directions are quotiented by the equivalence relation generated by the two pullback maps on directions. The file `Equalizers.lean` defines the equalizer object `EqObj`, the canonical map `eq : EqObj f g ⟶ P`, the induced lift `eqLift`, and the project-local universal-property theorem `eqObj_isEqualizer`.

- **Proof-engineering insight for equalizers**  
  The equalizer proof exposed an important Lean-specific design choice. The quotient on directions should depend only on the underlying position `a : P.A`, rather than on the full subtype witness showing that the two position maps agree at `a`. If the quotient depends on the proof witness itself, later arguments trigger fragile dependent transports. The final construction isolates the quotient/coequalizer behavior into helper definitions and lemmas, making the universal property proof much more stable.

## Relation to Mathlib

Mathlib already contains the unbundled notion of `PFunctor`, as well as general category-theoretic infrastructure for constructions such as equalizers, coequalizers, limits, and colimits. This project is therefore not trying to replace Mathlib’s abstract framework. Instead, it develops a concrete category `PolyC` of polynomial functors in the positions-and-directions presentation, together with explicit lens-style morphisms, semantic evaluation, algebraic constructors, and universal-property constructions.

The main difference from what is already in Mathlib is not “another polynomial datatype,” but rather the extra categorical structure built around it. The file `PFunctorBridge.lean` connects this development back to Mathlib’s `PFunctor`, so the long-term goal is not isolation from Mathlib but a clearer book-guided layer that can eventually interface more directly with Mathlib’s general category API.

## References

- Nelson Niu and David Spivak, *Polynomial Functors*  
- Mathlib4, especially the existing `PFunctor` development  
- The container/lens perspective from functional programming, which this project connects to the category-theoretic language of polynomial functors

## Future work

The next phase of the project is guided by Chapter 5 of *Polynomial Functors*, where the book develops limits and colimits in `Poly`. Now that the explicit equalizer construction is in place, the most natural immediate goal is to prove the **pointwise semantic equalizer theorem** suggested by Exercise 5.43. In Lean, this would say that for every type `X`, the semantic map `eval (EqObj f g) X → eval P X` is the equalizer of the two induced maps `eval P X → eval Q X`. This would connect the internal categorical construction in `PolyC` to the external semantic view of polynomial functors as type-level endofunctors.

After that, the next concrete construction from the book is **pullbacks**. The book’s pattern is that limits in `Poly` are built by taking limits on positions and colimits on directions, so pullbacks should be computed by taking pullbacks of positions and pushouts of directions. A `Pullbacks.lean` file would therefore be the natural continuation of `Equalizers.lean` and would make the project’s Chapter 5 story much more complete.

Once products, equalizers, and pullbacks are in place, the project can move toward a more explicit **finite-limits layer** for `PolyC`. The long-term goal there is not only to verify isolated constructions, but to make the pattern from the book reusable inside Lean: positions of a limit are computed by limits, while directions are computed by colimits. That would make the library more coherent mathematically and more useful as a foundation for later developments.

A second major direction is to strengthen the connection with **Mathlib**. Mathlib already contains `PFunctor` and the general category-theoretic infrastructure for equalizers, coequalizers, limits, and colimits. This project currently develops the polynomial category concretely and then bridges back to Mathlib through `PFunctorBridge.lean`. A strong next step would be to show that the explicit constructions in this repository match Mathlib’s abstract categorical ones more directly, for example by relating the explicit equalizer object to Mathlib’s equalizer API.

There is also room to continue the **algebraic structure** of the library. The project already includes sums, products, composition-style constructions, tensor-style structure, and related files for composition on morphisms and semantics. A natural continuation is to make these parts more uniform, prove more coherence-style results, and keep pushing the library toward the broader categorical structure emphasized in the book.

Finally, a longer-term stretch direction is to build a small **domain-specific language for polynomial expressions**. Such a DSL could encode sums, products, tensor-style operations, composition, constants, and representables, together with a denotation map into `PolyC`. That would make it possible to normalize polynomial expressions syntactically and then interpret them into Lean, reducing the amount of manual proof work required for algebraic identities.
## Build

```bash
lake update
lake build Poly
lake env lean Poly.lean
