# Erdős #953 / JSP-000793: formal bounds and growth exponent

This public repository records the Lean contribution submitted by
[`lixiang90`](https://github.com/lixiang90), prepared with Codex assistance.
It formalizes lower bounds for the area of a measurable subset of a
radius-`R` **open** disk in the Euclidean plane with no positive integer
distance between distinct points. It also combines these bounds with Allen
Hart's separately authored, pinned upper-bound formalization to prove the
logarithmic growth exponent. Hart's source is fetched from his repository for
local verification and is never committed here.

The principal statements are:

- `Erdos953Lower.erdos953_lower`: for every `ε > 0`, all sufficiently large
  disks contain an admissible set with area at least `cε R^(1/2-ε)`.
- `Erdos953Lower.erdos953_lower_polylog`: for `R ≥ 1000^4`, an admissible set
  exists with area at least `exp(-1) √R / [61440 (log R + 3)^8]`.
- `Erdos953Lower.lower_bound_for_Mopen` and
  `Erdos953Lower.lower_polylog_for_Mopen`: the same lower bounds for the
  supremum `Erdos953Lower.Mopen`, defined in `Erdos953Lower/Extremal.lean`.
- `Erdos953Lower.log_growth_exponent_of_bounds`: an abstract theorem that a
  square-root upper bound plus all `R^(1/2-ε)` lower bounds imply
  `log (F R) / log R → 1/2`. This theorem takes the upper bound as an explicit
  hypothesis.
- `Erdos953Formalization.erdos953_upper`: Hart's independently authored
  square-root upper bound, fetched at commit
  `0d031f7212150df788f4fa38c26cfc3fc729f3d0` and adapted locally to Lean
  `v4.32.2` using the small compatibility patch in this repository.
- `Erdos953Sandwich.growth_exponent_open`: the unconditional theorem
  `log (Mopen R) / log R → 1/2` as `R → ∞`, where `Mopen` is the supremum of
  admissible areas in the original open-disk formulation.
- `Erdos953Sandwich.polylog_sandwich_open`: explicit polylogarithmic lower
  bound and square-root upper bound for the same extremal function.

Use Python 3, Git, Lean `v4.32.2`, and the pinned `lake-manifest.json`. From a
clean checkout:

```sh
python scripts/prepare_hart.py
lake exe cache get
lake build Erdos953Growth
```

The first command checks out Hart's repository at its pinned commit, copies
only its Erdős #953 Lean modules into the Git-ignored local build tree, and
applies [`patches/hart-lean-4.32.2.patch`](patches/hart-lean-4.32.2.patch).
It does not alter the upstream checkout or redistribute Hart's source in this
repository. If you already have the exact Hart commit checked out, use
`python scripts/prepare_hart.py --hart-checkout /path/to/checkout` instead.
The patch changes only Lean-version compatibility details; the upper-bound
mathematics and proof remain Hart's.

The principal files include `#print axioms` checks. The checked theorems use
only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry` or
`admit` placeholders in the source.

The full project built successfully on 2026-09-30 (3,677 Lake jobs) using the
pinned Hart commit and an existing local pinned Mathlib checkout/cache. A
network-fresh dependency download has not yet been run for this copy.

The mathematical lower-bound route is Sárközy's digit construction, as
adapted to Erdős #953 in the [problem discussion](https://www.erdosproblems.com/953)
and compared with the modern exposition of
[Goenka–Moore](https://arxiv.org/abs/2605.06621). This Lean implementation
and its explicit polylogarithmic constant extraction were prepared in the
current research project. The mathematical square-root upper bound was given
by Przemek Chojecki in the [problem discussion](https://www.erdosproblems.com/forum/thread/953).
Its existing Lean formalization belongs to Allen Hart; see
[Hart's pinned project](https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/0d031f7212150df788f4fa38c26cfc3fc729f3d0/formalizations/erdos953).

The current lower-bound refinement keeps the leading digit magnitude in the
horizontal-coordinate estimate and uses vertical scale `8k` instead of
`8k²`. The formally proved distance gap is then `1/(48k³)` rather than
`1/(48k⁵)`. Thickening the digit points by disks of radius `1/(192k³)`
improves this implementation's explicit area loss from twelve to eight
powers of `log R`. The growth exponent remains `1/2`.

**Scope for prize review:** the growth-exponent theorem is unconditional and
fully checked when built with Hart's attributed upper proof, but the original
question asks for the largest area at a given radius and is currently listed
as open. This result does not assert an exact extremal area or a `Θ(√R)`
estimate. The lower construction and integration are our contribution; Hart's
upper formalization is his contribution. The accompanying PR asks the
maintainers whether this asymptotic result constitutes a complete answer under
the [award contribution rules](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md#external-solver-and-lean-submissions).
