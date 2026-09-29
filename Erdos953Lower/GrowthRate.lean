import Erdos953Lower.Asymptotic

/-!
An abstract growth-rate lemma for any nonnegative extremal function between
square-root upper and near-square-root lower bounds. This module depends only
on the original lower-bound project and mathlib, so it can be distributed
without including the separately authored upper-bound formalization.
-/

noncomputable section

open Filter
open scoped Topology

namespace Erdos953Lower

/-- A square-root upper bound and `R^(1/2-ε)` lower bounds for every positive
`ε` force logarithmic growth exponent `1/2`. Eventual positivity of `F` is
derived from the lower bound inside the proof. -/
theorem log_growth_exponent_of_bounds (F : ℝ → ℝ)
    (hupper : ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → F R ≤ C * Real.sqrt R)
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
        ∀ R : ℝ, R₀ ≤ R → c * R ^ (1 / 2 - ε) ≤ F R) :
    Tendsto (fun R : ℝ => Real.log (F R) / Real.log R)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hupper⟩ := hupper
  have hlogC :
      Tendsto (fun R : ℝ => Real.log C / Real.log R) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_const_nhds (x := Real.log C)).div_atTop Real.tendsto_log_atTop
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let ε : ℝ := ((1 / 2 : ℝ) - a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨c, hc, R₀, hlow⟩ := hlower ε hε
    have hlogc :
        Tendsto (fun R : ℝ => Real.log c / Real.log R) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_const_nhds (x := Real.log c)).div_atTop Real.tendsto_log_atTop
    have hsmall : ∀ᶠ R : ℝ in atTop, -ε < Real.log c / Real.log R :=
      (tendsto_order.1 hlogc).1 (-ε) (by linarith)
    filter_upwards [eventually_gt_atTop (max 1 R₀), hsmall] with R hR hs
    have hR1 : 1 < R := (le_max_left 1 R₀).trans_lt hR
    have hR₀ : R₀ ≤ R := (le_max_right 1 R₀).trans (le_of_lt hR)
    have hlogR : 0 < Real.log R := Real.log_pos hR1
    have hrpow : 0 < R ^ ((1 / 2 : ℝ) - ε) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hbound := hlow R hR₀
    have hlogbound := Real.log_le_log (mul_pos hc hrpow) hbound
    rw [Real.log_mul hc.ne' hrpow.ne', Real.log_rpow (by linarith : 0 < R)] at hlogbound
    have hs' : -ε * Real.log R < Real.log c :=
      (lt_div_iff₀ hlogR).1 hs
    apply (lt_div_iff₀ hlogR).2
    have heq : a = (1 / 2 : ℝ) - 2 * ε := by dsimp [ε]; ring
    rw [heq]
    nlinarith
  · intro b hb
    obtain ⟨c, hc, R₀, hlow⟩ := hlower (1 / 4) (by norm_num)
    have hsmall : ∀ᶠ R : ℝ in atTop,
        Real.log C / Real.log R < b - (1 / 2 : ℝ) :=
      (tendsto_order.1 hlogC).2 (b - (1 / 2 : ℝ)) (by linarith)
    filter_upwards [eventually_gt_atTop (max 1 R₀), hsmall] with R hR hs
    have hR1 : 1 < R := (le_max_left 1 R₀).trans_lt hR
    have hR₀ : R₀ ≤ R := (le_max_right 1 R₀).trans (le_of_lt hR)
    have hlogR : 0 < Real.log R := Real.log_pos hR1
    have hrpow : 0 < R ^ ((1 / 2 : ℝ) - 1 / 4) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hFpos : 0 < F R := (mul_pos hc hrpow).trans_le (hlow R hR₀)
    have hroot : 0 < Real.sqrt R := Real.sqrt_pos.2 (by linarith)
    have hlogbound := Real.log_le_log hFpos (hupper R (by linarith))
    rw [Real.log_mul hC.ne' hroot.ne', Real.log_sqrt (by linarith : 0 ≤ R)] at hlogbound
    have hs' : Real.log C < (b - (1 / 2 : ℝ)) * Real.log R :=
      (div_lt_iff₀ hlogR).1 hs
    apply (div_lt_iff₀ hlogR).2
    nlinarith

#print axioms log_growth_exponent_of_bounds

end Erdos953Lower
