# Erdős #953 / JSP-000793: a standalone Lean lower bound

This public repository records the Lean contribution submitted by
[`lixiang90`](https://github.com/lixiang90), prepared with Codex assistance.
It formalizes lower bounds for the area of a measurable subset of a
radius-`R` **open** disk in the Euclidean plane with no positive integer
distance between distinct points. It contains only the lower construction and
its consequences. The package has no dependency on Allen Hart's separately
authored upper-bound formalization.

The principal statements are:

- `Erdos953Lower.erdos953_lower`: for every `ε > 0`, all sufficiently large
  disks contain an admissible set with area at least `cε R^(1/2-ε)`.
- `Erdos953Lower.erdos953_lower_polylog`: for `R ≥ 1000^4`, an admissible set
  exists with area at least `exp(-1) √R / [100000 (log R + 3)^12]`.
- `Erdos953Lower.lower_bound_for_Mopen` and
  `Erdos953Lower.lower_polylog_for_Mopen`: the same lower bounds for the
  supremum `Erdos953Lower.Mopen`, defined in `Erdos953Lower/Extremal.lean`.
- `Erdos953Lower.log_growth_exponent_of_bounds`: an abstract theorem that a
  square-root upper bound plus all `R^(1/2-ε)` lower bounds imply
  `log (F R) / log R → 1/2`. This theorem takes the upper bound as an explicit
  hypothesis; this package does **not** prove that upper bound.

Use Lean `v4.32.2` and the pinned `lake-manifest.json`. From a clean checkout:

```sh
lake exe cache get
lake build Erdos953Lower
```

The principal files include `#print axioms` checks. The checked theorems use
only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry` or
`admit` placeholders in the source.

This source-only package was built on 2026-09-29 from a separate directory
using the same pinned Mathlib checkout as the research workspace; the local
build completed successfully (3,443 Lake jobs). A network-fresh dependency
download has not yet been run for this copy.

The mathematical lower-bound route is Sárközy's digit construction, as
adapted to Erdős #953 in the [problem discussion](https://www.erdosproblems.com/953)
and compared with the modern exposition of
[Goenka–Moore](https://arxiv.org/abs/2605.06621). This Lean implementation
and its explicit polylogarithmic constant extraction were prepared in the
current research project. The mathematical growth-exponent upper bound and
its existing Lean formalization have separate provenance; see
[Hart's project](https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/0d031f7212150df788f4fa38c26cfc3fc729f3d0/formalizations/erdos953).

**Scope for prize review:** this package alone is a lower-bound contribution.
The theorem `log_growth_exponent_of_bounds` assumes an upper bound and does not
instantiate it for the extremal area. A separate local integration checked the
growth-exponent theorem using Allen Hart's independently authored upper proof,
but Hart's source is not included here. The original question asks for the
largest area at a given radius and is currently listed as open; these results
do not assert an exact extremal area, a `Θ(√R)` estimate, a complete proof of
the original problem, or prize eligibility. The accompanying PR requests the
maintainers' assessment under the [award contribution rules](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md#external-solver-and-lean-submissions).
