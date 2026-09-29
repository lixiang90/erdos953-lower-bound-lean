# Source and attribution

The package contains the `Erdos953Lower/` directory and
`Erdos953Lower.lean`, developed in a separate research workspace and published
here on 2026-09-29 by the submitting GitHub account `lixiang90` with Codex
assistance. The repository also contains our open/closed-disk bridge,
upper/lower combination, and growth-exponent theorem. No Hart source file is
committed here.

The mathematical lower-bound strategy is attributed to Sárközy, with the
problem-specific adaptation discussed by Junnosuke Koizumi and Vjekoslav
Kovac in [Erdős #953](https://www.erdosproblems.com/953). The source code is a
new Lean implementation prepared for this submission. No mathematical
discovery or formalization authorship is claimed for Hart's upper bound. The
abstract growth-rate lemma and the standalone extremal definition are original
to this package.

The upper-bound theorem and its Lean proof are fetched at the pinned Hart
commit by `scripts/prepare_hart.py` into an ignored build directory. The small
`patches/hart-lean-4.32.2.patch` is our compatibility adaptation for the newer
Lean/Mathlib version and does not transfer Hart's proof authorship. The
referenced repository does not advertise a license at this commit; this
repository therefore does not redistribute its full source.
