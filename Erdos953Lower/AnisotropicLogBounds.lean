import Erdos953Lower.AnisotropicSelection
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum

namespace Erdos953Lower
noncomputable section
set_option maxHeartbeats 400000

def logSeriesLower (x : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range 6, ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1)

def logSeriesUpper (x : ℝ) : ℝ :=
  logSeriesLower x + 2 * ((x - 1) / (x + 1)) ^ 13 /
    (1 - ((x - 1) / (x + 1)) ^ 2)

theorem log_series_bounds (x : ℝ) (hx : 1 ≤ x) :
    logSeriesLower x ≤ Real.log x ∧ Real.log x ≤ logSeriesUpper x := by
  let z := (x - 1) / (x + 1)
  have hx0 : 0 < x := by linarith only [hx]
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z < 1 := by
    dsimp [z]
    apply (div_lt_iff₀ (by positivity : 0 < x + 1)).2
    linarith only [hx]
  have hid : (1 + z) / (1 - z) = x := by
    dsimp [z]
    field_simp
    ring
  have hl := Real.sum_range_le_log_div hz0 hz1 6
  have hu := Real.log_div_le_sum_range_add hz0 hz1 6
  rw [hid] at hl hu
  constructor
  · unfold logSeriesLower
    change 2 * (∑ i ∈ Finset.range 6, z ^ (2 * i + 1) / (2 * i + 1)) ≤ _
    linarith only [hl]
  · unfold logSeriesUpper logSeriesLower
    change _ ≤ 2 * (∑ i ∈ Finset.range 6, z ^ (2 * i + 1) / (2 * i + 1)) +
      2 * z ^ 13 / (1 - z ^ 2)
    norm_num only at hu
    rw [mul_div_assoc]
    linarith only [hu]

/-- A rational certificate for a logarithm, checked entirely by the kernel. -/
theorem certify_log_bounds (x : ℝ) (m : ℕ) (lo hi : ℝ)
    (hy : 1 ≤ x / 2 ^ m)
    (hl : lo ≤ (m : ℝ) * logSeriesLower 2 + logSeriesLower (x / 2 ^ m))
    (hu : (m : ℝ) * logSeriesUpper 2 + logSeriesUpper (x / 2 ^ m) ≤ hi) :
    lo ≤ Real.log x ∧ Real.log x ≤ hi := by
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hx0 : 0 < x := by
    have h : (2 : ℝ) ^ m ≤ x := by simpa only [one_mul] using (le_div_iff₀ hpow).1 hy
    exact hpow.trans_le h
  have h2 := log_series_bounds 2 (by norm_num)
  have hY := log_series_bounds (x / 2 ^ m) hy
  have heq : Real.log x = (m : ℝ) * Real.log 2 + Real.log (x / 2 ^ m) := by
    rw [Real.log_div hx0.ne' hpow.ne', Real.log_pow]
    ring
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  constructor
  · have hmul := mul_le_mul_of_nonneg_left h2.1 hm
    linarith only [hl, hmul, hY.1, heq]
  · have hmul := mul_le_mul_of_nonneg_left h2.2 hm
    linarith only [hu, hmul, hY.2, heq]

/-- The maximum-base reduction uses only the tangent inequality for log. -/
theorem base_log_function_mono (c d x y : ℝ)
    (hc : 0 ≤ c) (hd : 1 ≤ d) (hx : 0 < x) (hxy : x ≤ y)
    (hlogx : 1 ≤ Real.log x) :
    x * (Real.log (c + d * Real.log x) / (c + d * Real.log x)) ≤
      y * (Real.log (c + d * Real.log y) / (c + d * Real.log y)) := by
  let X := c + d * Real.log x
  let Y := c + d * Real.log y
  have hy : 0 < y := hx.trans_le hxy
  have hdx : d ≤ X := by
    dsimp [X]
    nlinarith only [hc, hd, hlogx]
  have hX1 : 1 ≤ X := hd.trans hdx
  have hX0 : 0 < X := by linarith only [hX1]
  have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  have hXY : X ≤ Y := by
    dsimp [X, Y]
    simpa only [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hlogxy (by linarith only [hd])) c
  have hY0 : 0 < Y := hX0.trans_le hXY
  have hratio0 : 0 ≤ y / x - 1 := by
    have h : (1 : ℝ) ≤ y / x := (le_div_iff₀ hx).2 (by simpa only [one_mul] using hxy)
    linarith only [h]
  have htan := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at htan
  have hscale := mul_le_mul_of_nonneg_right hdx hratio0
  have hlogscale := mul_le_mul_of_nonneg_left htan (by linarith only [hd] : 0 ≤ d)
  have hYbound : Y ≤ X * (y / x) := by
    dsimp [X, Y] at *
    nlinarith only [hscale, hlogscale]
  have hcross : x * Y ≤ y * X := by
    have h := mul_le_mul_of_nonneg_right hYbound hx.le
    field_simp at h
    nlinarith only [h]
  have hquot : x / X ≤ y / Y := (div_le_div_iff₀ hX0 hY0).2 (by nlinarith only [hcross])
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlogXY : Real.log X ≤ Real.log Y := Real.log_le_log hX0 hXY
  have hprod := mul_le_mul hquot hlogXY hlogX (div_nonneg hy.le hY0.le)
  dsimp [X, Y] at hprod
  simpa only [div_mul_eq_mul_div, mul_div_assoc, mul_comm] using hprod

theorem base_bound_from_max (T : ℝ) (n k K : ℕ)
    (hn : 6 ≤ n) (hnk : 2 * n ≤ k) (hkK : k ≤ K)
    (hbudget : Real.log 10 + (2 * n : ℝ) * Real.log k ≤ T)
    (hcert : (K : ℝ) * Real.log (Real.log 10 + (2 * n : ℝ) * Real.log K) <
      2 * (Real.log 10 + (2 * n : ℝ) * Real.log K)) :
    (k : ℝ) < 2 * T / Real.log T := by
  have hk12 : (12 : ℝ) ≤ k := by exact_mod_cast (by omega : 12 ≤ k)
  have hk0 : (0 : ℝ) < k := by linarith only [hk12]
  have hlogk : 1 ≤ Real.log k := by
    apply (Real.le_log_iff_exp_le hk0).2
    exact Real.exp_one_lt_three.le.trans (by linarith only [hk12])
  have hn12 : (12 : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : 12 ≤ 2 * n)
  have hlog10 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  let t := Real.log 10 + (2 * n : ℝ) * Real.log k
  let u := Real.log 10 + (2 * n : ℝ) * Real.log K
  have ht12 : 12 ≤ t := by dsimp [t]; nlinarith only [hn12, hlog10, hlogk]
  have ht0 : 0 < t := by linarith only [ht12]
  have htu : t ≤ u := by
    dsimp [t, u]
    gcongr
  have hu0 : 0 < u := ht0.trans_le htu
  have hT12 : 12 ≤ T := ht12.trans hbudget
  have hT0 : 0 < T := by linarith only [hT12]
  have hlogT0 : 0 < Real.log T := Real.log_pos (by linarith only [hT12])
  have hanti := Real.log_div_self_antitoneOn
    (show t ∈ Set.Ici (Real.exp 1) from Real.exp_one_lt_three.le.trans
      (by linarith only [ht12]))
    (show T ∈ Set.Ici (Real.exp 1) from Real.exp_one_lt_three.le.trans
      (by linarith only [hT12])) hbudget
  have hantiK := mul_le_mul_of_nonneg_left hanti hk0.le
  have hmono := base_log_function_mono (Real.log 10) (2 * n : ℝ) (k : ℝ) (K : ℝ)
    hlog10 (by linarith only [hn12]) hk0 (by exact_mod_cast hkK) hlogk
  have hlast : (K : ℝ) * (Real.log u / u) < 2 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hu0).2
    exact hcert
  have hchain : (k : ℝ) * (Real.log T / T) < 2 :=
    hantiK.trans_lt (hmono.trans_lt hlast)
  have hcross : (k : ℝ) * Real.log T < 2 * T := by
    have h := (div_lt_iff₀ hT0).1 (show (k : ℝ) * Real.log T / T < 2 by
      simpa only [mul_div_assoc] using hchain)
    exact h
  exact (lt_div_iff₀ hlogT0).2 hcross

#print axioms certify_log_bounds
#print axioms base_bound_from_max
end
end Erdos953Lower
