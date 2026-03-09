# TODO — EE598 Poly Project Plan (Ordered)

## Milestone 0 — Repo + build sanity
- [ ] Project builds locally with `lake build`
- [ ] Repo is pushed to GitHub (private)
- [ ] Eric added as collaborator and confirmed access

## Milestone 1 — Core data model (positions/directions)
- [ ] Define `Poly` as a container: `Pos : Type`, `Dir : Pos → Type`
- [ ] Define the extension/semantics: `⟦P⟧ X = Σ a : Pos, (Dir a → X)`
- [ ] Define `map` for the semantics and prove functor laws (id/comp)

## Milestone 2 — Morphisms as lenses
- [ ] Define `Lens P Q` with:
      - `onPos : P.Pos → Q.Pos`
      - `onDir : ∀ a, Q.Dir (onPos a) → P.Dir a`
- [ ] Define how a lens induces a function `⟦P⟧ X → ⟦Q⟧ X`
- [ ] Define identity lens and composition of lenses
- [ ] Prove lens composition is associative and identities behave correctly

## Milestone 3 — Category structure
- [ ] Package the above into a “category of polynomials” interface
- [ ] (If using Mathlib) provide `instance : Category Poly`

## Milestone 4 — Basic constructors + examples
- [ ] Define constant polynomial, identity polynomial, coproduct/sum, product (as containers)
- [ ] Test with small examples (lists, options, finite arities)

## Stretch goals (only if time)
- [ ] Define composition product (polynomial composition) and show closure
- [ ] Relate lens definition to natural transformations more explicitly
- [ ] Explore limits/colimits behavior on positions/directions
