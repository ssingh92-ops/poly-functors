# TODO — EE598 Poly Project (Book-Aligned)

## ✅ Milestone 0 — Repo + build sanity
- [x] Project builds locally with `lake build`
- [x] Repo is pushed to GitHub (private)
- [x] Eric added as collaborator and confirmed access

## ✅ Milestone 1 — Core containers + lenses (done)
- [x] `PolyC` as (shapes A, positions B)
- [x] semantics `eval : X ↦ Σ a, (B a → X)`
- [x] lens morphisms `Hom` + `map`
- [x] category instance `Category PolyC`

## ✅ Milestone 2 — Evaluation as functor + semantics embedding (mostly done)
- [x] `evalFunctor : Type ⥤ Type`
- [x] naturality lemma for `map`
- [x] `homToNatTrans` and `Sem : PolyC ⥤ (Type ⥤ Type)` (after Semantics file compiles)

## ✅ Milestone 3 — Algebraic constructors (done, but now formalize universal properties)
- [x] `sum`, `prod`, `composeObj` + evaluation equivalences

## ✅ Milestone 4 — Universal properties in PolyC (nontrivial, category-theoretic)
- [x] Prove `sum` is a coproduct in `PolyC` (explicit injections + UP)
- [x] Prove `prod` is a product in `PolyC` (explicit projections + UP)
- [x] Clean statements: `Hom (sum P Q) R ≃ Hom P R × Hom Q R`, etc.

## ✅ Milestone 5 — Parallel product ⊗ (Dirichlet product) + symmetric monoidal structure
- [x] Define `⊗` on objects and morphisms
- [x] Define unit polynomial `y`
- [x] Construct isomorphisms: left/right unitor, associator, braiding
- [x] Prove distributivity over sums: `(P + Q) ⊗ R ≅ (P ⊗ R) + (Q ⊗ R)` (or similar)

## ✅ Milestone 6 — Composition product ⊳ (monoidal structure from composition)
- [x] Extend `composeObj` to a bifunctor on morphisms (hard part!)
- [x] Construct associator/unitor isomorphisms for ⊳
- [x] Show `eval` respects composition up to iso (already have object-level equivalence)

## Milestone 7 — pick ONE major theorem
- [ ] Option A: Cartesian closedness (exponentials) for Poly (book Thm 5.32 style)
- [x] Option B: Equalizers / limits characterization (“positions limit, directions colimit”)

## Polishing / usability
- [ ] Reduce `import Mathlib` in Core to narrower imports (optional performance cleanup)
- [ ] Add `Poly/README.md` or module comments describing dependency graph
- [ ] Add a few runnable examples and sanity checks
