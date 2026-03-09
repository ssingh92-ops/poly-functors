# TODO — EE598 Poly Project Plan (Ordered)

## Milestone 0 — Repo + build sanity
- [x] Project builds locally with `lake build`
- [x] Repo is pushed to GitHub (private)
- [x] Eric added as collaborator and confirmed access

## Milestone 1 — Core data model (positions/directions)
- [x] Define `Poly` as a container: `Pos : Type`, `Dir : Pos → Type`  (done as `PolyC`)
- [x] Define the extension/semantics: `⟦P⟧ X = Σ a : Pos, (Dir a → X)`  (done as `eval`)
- [x] Define `map` for the semantics and prove functor laws (id/comp)  (done as `evalFunctor`)

## Milestone 2 — Morphisms as lenses
- [x] Define `Lens P Q` with forward-on-shapes and backward-on-positions  (done as `Hom`)
- [x] Define how a lens induces a function `⟦P⟧ X → ⟦Q⟧ X`  (done as `map`)
- [x] Define identity lens and composition of lenses  (done as `id`, `comp`)
- [x] Prove lens composition is associative and identities behave correctly  (done via `Category`)

## Milestone 3 — Category structure
- [x] Package into a category of polynomials  (done: `instance : Category PolyC`)

## Milestone 4 — Basic constructors + examples
- [x] Define coproduct/sum and product (as containers)  (`sum`, `prod`)
- [x] Verify evaluation laws for sum/product  (`evalSumEquiv`, `evalProdEquiv`)
- [x] Define container composition (substitution)  (`composeObj`, `evalComposeEquiv`)
- [ ] Add explicit constant/identity polynomials and small “real” examples (list-like, maybe-like)

## Stretch goals (only if time)
- [ ] Package the semantics as a functor `PolyC ⥤ (Type ⥤ Type)` (lenses ↦ NatTrans)
- [ ] Relate lens definition to natural transformations more explicitly (injective/faithful statement, optional equivalence under choice)
- [ ] Explore limits/colimits behavior on positions/directions
- [ ] Explore connecting theorem to Locally Closed Cartesian Coordinates
