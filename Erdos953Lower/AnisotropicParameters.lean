/- Elementary counting estimates for simultaneous base/length selection.
This module assumes parameters with `2n ≤ k`; it does not yet formalize
the existence of the maximal n used in the research note. -/
import Erdos953Lower.AnisotropicGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Erdos953Lower

set_option maxHeartbeats 50000

/-- Bernoulli's inequality in the precise form needed for the digit count. -/
theorem one_sub_nat_mul_le_pow (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * t ≤ (1 - t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmul := mul_le_mul_of_nonneg_right ih (by linarith only [ht1] : 0 ≤ 1 - t)
    have hpos : 0 ≤ (n : ℝ) * t ^ 2 := by positivity
    rw [pow_succ]
    push_cast
    nlinarith only [hmul, hpos]

/-- When the base is at least twice the length, omitting one digit costs
at most half of the full count. -/
theorem half_pow_le_sub_one_pow (k : ℝ) (n : ℕ) (hk : 1 ≤ k)
    (hnk : 2 * (n : ℝ) ≤ k) :
    k ^ n / 2 ≤ (k - 1) ^ n := by
  have hk0 : 0 < k := by linarith only [hk]
  have ht0 : 0 ≤ 1 / k := by positivity
  have ht1 : 1 / k ≤ 1 := (div_le_iff₀ hk0).2 (by linarith only [hk])
  have hbern := one_sub_nat_mul_le_pow (1 / k) ht0 ht1 n
  have hnquot : (n : ℝ) / k ≤ 1 / 2 :=
    (div_le_iff₀ hk0).2 (by linarith only [hnk])
  have hhalf : 1 / 2 ≤ (1 - 1 / k) ^ n := by
    have hbern' : 1 - (n : ℝ) / k ≤ (1 - 1 / k) ^ n := by
      simpa only [mul_one_div] using hbern
    linarith only [hbern', hnquot]
  have hmul := mul_le_mul_of_nonneg_right hhalf (pow_nonneg hk0.le n)
  have hid : (1 - 1 / k) ^ n * k ^ n = (k - 1) ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hid] at hmul
  linarith only [hmul]

/-- The two Bernoulli estimates eliminate the old radius-grid factor.
The hypothesis is `A < (k+1)^(2n)`, as supplied by taking an integer root. -/
theorem anisotropic_digit_count_lower (A k : ℝ) (n : ℕ)
    (hA : 0 ≤ A) (hk : 1 ≤ k) (hnk : 2 * (n : ℝ) ≤ k)
    (hgrid : A < (k + 1) ^ (2 * n)) :
    Real.sqrt A / 4 < (k - 1) ^ n := by
  have h₁ := half_pow_le_sub_one_pow k n hk hnk
  have h₂ := half_pow_le_sub_one_pow (k + 1) n
    (by linarith only [hk]) (by linarith only [hnk])
  have h₂' : (k + 1) ^ n / 2 ≤ k ^ n := by
    simpa only [add_sub_cancel_right] using h₂
  have hpow : (k + 1) ^ (2 * n) = ((k + 1) ^ n) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hpow] at hgrid
  have hs0 := Real.sqrt_nonneg A
  have hs2 := Real.sq_sqrt hA
  have hkp0 : 0 ≤ (k + 1) ^ n := by positivity
  have hroot : Real.sqrt A < (k + 1) ^ n := by
    nlinarith only [hgrid, hs0, hs2, hkp0]
  linarith only [h₁, h₂', hroot]

#print axioms one_sub_nat_mul_le_pow
#print axioms half_pow_le_sub_one_pow
#print axioms anisotropic_digit_count_lower

end Erdos953Lower
