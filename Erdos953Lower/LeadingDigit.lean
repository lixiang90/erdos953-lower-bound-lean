/-
  Erdős Problem 953: a leading signed digit dominates all lower digits.
-/
import Erdos953Lower.DigitTail
import Erdos953Lower.DigitControl

namespace Erdos953Lower

open Finset

/-- Quantitative control of a signed base-k expansion through its highest
nonzero coefficient. The lower bound is deliberately weak but sufficient
for a fixed distance gap after the parameter k has been chosen. -/
theorem leading_linear_bounds (k i : ℕ) (d : ℕ → ℤ)
    (hk : 3 ≤ k)
    (hlow : ∀ j < i, |d j| ≤ (k : ℤ) - 2)
    (hdi : d i ≠ 0) :
    (k : ℤ) ^ i ≤ (k : ℤ) * |∑ j ∈ range (i + 1), d j * (k : ℤ) ^ j| ∧
    |∑ j ∈ range (i + 1), d j * (k : ℤ) ^ j| ≤
      2 * |d i| * (k : ℤ) ^ i := by
  let K : ℤ := k
  let S : ℤ := ∑ j ∈ range i, K ^ j
  let T : ℤ := ∑ j ∈ range i, d j * K ^ j
  let U : ℤ := ∑ j ∈ range (i + 1), d j * K ^ j
  have hK : 3 ≤ K := by
    change (3 : ℤ) ≤ (k : ℤ)
    exact_mod_cast hk
  have hK0 : 0 ≤ K := by omega
  have hpow : 0 ≤ K ^ i := pow_nonneg hK0 i
  have hS : 0 ≤ S := by
    dsimp [S]
    apply sum_nonneg
    intro j hj
    positivity
  have htail : |T| ≤ (K - 2) * S := by
    exact weighted_digit_sum_abs_le K (K - 2) i d hK0 hlow
  have hgeom : S * (K - 1) + 1 = K ^ i := by
    simpa [S] using geom_sum_mul_add (K - 1) i
  have hsum : U = T + d i * K ^ i := by
    simp [U, T, sum_range_succ]
  have hD : 1 ≤ |d i| := by
    have : 0 < |d i| := abs_pos.mpr hdi
    omega
  have hmain : |d i * K ^ i| = |d i| * K ^ i := by
    rw [abs_mul, abs_of_nonneg hpow]
  have htriangle : |U| ≤ |T| + |d i * K ^ i| := by
    rw [hsum]
    exact abs_add_le _ _
  have hreverse : |d i * K ^ i| ≤ |U| + |T| := by
    calc
      |d i * K ^ i| = |U - T| := by rw [hsum]; congr 1; abel
      _ ≤ |U| + |T| := by
        simpa [sub_eq_add_neg] using (abs_add_le U (-T))
  have hDpow : K ^ i ≤ |d i| * K ^ i := by
    nlinarith [mul_nonneg (show 0 ≤ |d i| - 1 by omega) hpow]
  have hLower : S + 1 ≤ |U| := by
    rw [hmain] at hreverse
    nlinarith
  have hMultiply : 0 ≤ K * (|U| - (S + 1)) :=
    mul_nonneg hK0 (by linarith)
  have hUpper : |U| ≤ 2 * |d i| * K ^ i := by
    rw [hmain] at htriangle
    nlinarith
  constructor
  · change K ^ i ≤ K * |U|
    nlinarith
  · simpa [U, K] using hUpper

/-- The leading digit magnitude can be retained in the linear lower bound.
It may improve the eventual square-root gap when propagated through the construction. -/
theorem leading_linear_weighted_lower (k i : ℕ) (d : ℕ → ℤ)
    (hk : 3 ≤ k)
    (hlow : ∀ j < i, |d j| ≤ (k : ℤ) - 2)
    (hdi : d i ≠ 0) :
    |d i| * (k : ℤ) ^ i ≤
      (k : ℤ) * |∑ j ∈ range (i + 1), d j * (k : ℤ) ^ j| := by
  let K : ℤ := k
  let S : ℤ := ∑ j ∈ range i, K ^ j
  let T : ℤ := ∑ j ∈ range i, d j * K ^ j
  let U : ℤ := ∑ j ∈ range (i + 1), d j * K ^ j
  have hK : 3 ≤ K := by
    change (3 : ℤ) ≤ (k : ℤ)
    exact_mod_cast hk
  have hS : 0 ≤ S := by
    dsimp [S]
    apply sum_nonneg
    intro j hj
    positivity
  have hpow : 0 ≤ K ^ i := pow_nonneg (by omega) i
  have htail : |T| ≤ (K - 2) * S :=
    weighted_digit_sum_abs_le K (K - 2) i d (by omega) hlow
  have hgeom : S * (K - 1) + 1 = K ^ i := by
    simpa [S] using geom_sum_mul_add (K - 1) i
  have hTleX : |T| ≤ K ^ i := by
    nlinarith [htail, hgeom, hS]
  have hsum : U = T + d i * K ^ i := by
    simp [U, T, sum_range_succ]
  have hD : 1 ≤ |d i| := by
    have : 0 < |d i| := abs_pos.mpr hdi
    omega
  have hreverse : |d i| * K ^ i ≤ |U| + |T| := by
    have habs : |d i * K ^ i| = |d i| * K ^ i := by
      rw [abs_mul, abs_of_nonneg hpow]
    calc
      |d i| * K ^ i = |d i * K ^ i| := habs.symm
      _ = |U - T| := by rw [hsum]; congr 1; abel
      _ ≤ |U| + |T| := by
        simpa [sub_eq_add_neg] using (abs_add_le U (-T))
  by_cases hD1 : |d i| = 1
  · have hlin := leading_linear_bounds k i d hk hlow hdi
    dsimp [K, U] at *
    rw [hD1]
    simpa using hlin.1
  · have hD2 : 2 ≤ |d i| := by omega
    have hD2X : 0 ≤ (|d i| - 2) * K ^ i :=
      mul_nonneg (by omega) hpow
    have h2 : |d i| * K ^ i ≤ 2 * |U| := by
      nlinarith [hreverse, hTleX, hD2X]
    have hK2 : 2 * |U| ≤ K * |U| := by
      nlinarith [mul_nonneg (show 0 ≤ K - 2 by omega) (abs_nonneg U)]
    exact h2.trans hK2

/-- The squared-place sum retains at least half of its leading digit and
at most twice that digit. -/
theorem leading_quadratic_bounds (k i : ℕ) (d : ℕ → ℤ)
    (hk : 3 ≤ k)
    (hlow : ∀ j < i, |d j| ≤ (k : ℤ) - 2)
    (hdi : d i ≠ 0) :
    |d i| * (((k : ℤ) ^ 2) ^ i) ≤
      2 * |∑ j ∈ range (i + 1), d j * (((k : ℤ) ^ 2) ^ j)| ∧
    |∑ j ∈ range (i + 1), d j * (((k : ℤ) ^ 2) ^ j)| ≤
      2 * |d i| * (((k : ℤ) ^ 2) ^ i) := by
  let q : ℤ := (k : ℤ) ^ 2
  let S : ℤ := ∑ j ∈ range i, q ^ j
  let T : ℤ := ∑ j ∈ range i, d j * q ^ j
  let U : ℤ := ∑ j ∈ range (i + 1), d j * q ^ j
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpow : 0 ≤ q ^ i := pow_nonneg hq i
  have htail : |T| ≤ ((k : ℤ) - 2) * S :=
    weighted_digit_sum_abs_le q ((k : ℤ) - 2) i d hq hlow
  have hgap : 2 * ((k : ℤ) - 2) * S < q ^ i := by
    simpa [q, S] using quadratic_digit_tail k i hk
  have hsum : U = T + d i * q ^ i := by
    simp [U, T, sum_range_succ]
  have hD : 1 ≤ |d i| := by
    have : 0 < |d i| := abs_pos.mpr hdi
    omega
  have hmain : |d i * q ^ i| = |d i| * q ^ i := by
    rw [abs_mul, abs_of_nonneg hpow]
  have htriangle : |U| ≤ |T| + |d i * q ^ i| := by
    rw [hsum]
    exact abs_add_le _ _
  have hreverse : |d i * q ^ i| ≤ |U| + |T| := by
    calc
      |d i * q ^ i| = |U - T| := by rw [hsum]; congr 1; abel
      _ ≤ |U| + |T| := by
        simpa [sub_eq_add_neg] using (abs_add_le U (-T))
  rw [hmain] at htriangle hreverse
  have hDpow : q ^ i ≤ |d i| * q ^ i := by
    nlinarith [mul_nonneg (show 0 ≤ |d i| - 1 by omega) hpow]
  constructor
  · change |d i| * q ^ i ≤ 2 * |U|
    nlinarith
  · change |U| ≤ 2 * |d i| * q ^ i
    nlinarith

#print axioms leading_linear_bounds
#print axioms leading_linear_weighted_lower
#print axioms leading_quadratic_bounds

end Erdos953Lower
