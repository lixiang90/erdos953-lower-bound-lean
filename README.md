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

- `Erdos953Lower.fixed_unbounded_uniform_lower`: a single fixed unbounded
  open set avoids every positive integer distance and, for **every real
  `R ≥ exp 1`**, has area in the radius-`R` disk at least
  `9/9604 · √R · (log(log R) / log R)^3`.
- `Erdos953Lower.retreat_lower_Mopen`: the same improved lower bound for
  the standalone extremal area. Its coefficient is about `0.00093711`,
  a factor `124416/2401 ≈ 51.8184` above the earlier fixed infinite
  construction's `1/55296`. This improves the coefficient, not the order;
  it does not assert global optimality.
- `Erdos953SharpLower.sharp_lower_Mopen`: for every real `R ≥ exp 1`,
  `Mopen R ≥ √R / (32768 √10) · (log(log R) / log R)^3`.
- `Erdos953SharpLower.explicit_lower_all_radii`: for every `R > 0`, the
  lower bound is `πR²` when `R ≤ 1/2`, `π/4` when `1/2 < R < exp 1`, and
  the maximum of `π/4` and the preceding logarithmic expression thereafter.
- `Erdos953SharpLower.sharp_lower_standalone` and
  `Erdos953SharpLower.explicit_lower_standalone`: the same results for the
  independently defined `Erdos953Lower.Mopen`.
- `Erdos953SharpLower.digit_rectangle_lower`: for integers `k ≥ 3`, `n ≥ 0`
  and `10 k^(2n) ≤ R`, the thin-rectangle construction gives area
  `(k-1)^n / (1024 k^3)`. For example, the fully checked construction at
  `R = 10^18` has area `170859375/4194304 = 40.7360494136810302734375`.
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

The trimmed, vertically compressed construction is in `Erdos953Retreat.lean`
and the seven `Erdos953Lower/Retreat*.lean` support modules. It can be
checked separately with `lake build Erdos953Retreat`, without fetching or
importing Hart's upper-bound project. The default build includes it.
The paper source and compiled PDF are in
[`paper/retreat-uniform-lower-bound.tex`](paper/retreat-uniform-lower-bound.tex)
and [`paper/retreat-uniform-lower-bound.pdf`](paper/retreat-uniform-lower-bound.pdf).
Run `python scripts/build_paper.py` with an existing `pdflatex` installation
to rebuild the PDF with resolved references. The paper's family optimization
limit `384 exp(-3/2)` is an analytic result; its asymptotic argument is not
included in the Lean verification claim. The simple area-`3/8` prefix used
in Lean replaces the larger finite computational prefix while retaining the
same `9/9604` guaranteed coefficient.

The full project built successfully on 2026-10-04 (3,696 Lake jobs), including
the fixed unbounded set and its `9/9604` uniform theorem, using the
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

The earlier lower-bound refinement keeps the leading digit magnitude in the
horizontal-coordinate estimate and uses vertical scale `8k` instead of
`8k²`. The formally proved distance gap is then `1/(48k³)` rather than
`1/(48k⁵)`. Thickening the digit points by disks of radius `1/(192k³)`
improves this implementation's explicit area loss from twelve to eight
powers of `log R`.

The new refinement thickens those same centers by rectangles of width `1/4`
and height `1/(256k^3)`. It proves the exact union area, a sharper radius
bound, and the existence of a simultaneous choice of base and digit length
at arbitrary real radii. The resulting explicit loss is
`(log R / log(log R))^3`, with the coefficient above. The final theorem
combines a rectangle witness for `R ≥ 10^14` with a half-unit disk estimate
below that threshold. All ten exceptional base estimates are proved from
Mathlib's logarithm-series remainder and rational arithmetic inside Lean.
The checked source needs no external numerical oracle or certificate input.
The growth exponent remains `1/2`.

The complete new result is in `Erdos953SharpLower.lean`; its geometric,
parameter-selection, and numerical dependencies are the
`Erdos953Lower/Anisotropic*.lean` modules. The default `lake build` and the
existing `lake build Erdos953Growth` both include this result.

The [research snapshot](research/README.md) preserves the subsequent fixed-set,
small-radius, upper-bound and local-exchange investigations, with scripts,
exact certificates, independent audit reports and a complete compressed data
archive. The latest fill-and-cropped-exchange construction adds approximately
`0.3561647541325377` of area to the previous fixed unbounded set for every
`R >= 268435456`, while preserving its uniform lower bound. These experiments
are separately audited in Python and have not been formalized in Lean; their
finite modifications do not establish a new asymptotic order.

**Scope for prize review:** the growth-exponent theorem is unconditional and
fully checked when built with Hart's attributed upper proof, but the original
question asks for the largest area at a given radius and is currently listed
as open. This result does not assert an exact extremal area or a `Θ(√R)`
estimate. The lower construction and integration are our contribution; Hart's
upper formalization is his contribution. The accompanying PR asks the
maintainers whether this asymptotic result constitutes a complete answer under
the [award contribution rules](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md#external-solver-and-lean-submissions).
