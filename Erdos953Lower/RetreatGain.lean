import Erdos953Lower.RetreatGeometry
import Erdos953Lower.AnisotropicLogBounds

namespace Erdos953Lower
noncomputable section
set_option maxHeartbeats 500000

def retreatArea (k n t : ℕ) : ℝ :=
  ((k : ℝ) - t)^n * retreatHeight k t / 2

def referenceArea (k n : ℕ) : ℝ :=
  ((k : ℝ)-1)^n / (108*(k : ℝ)^3)

def retreatGain : ℝ := 124416/2401

theorem retreat_ratio_lower (k n : ℕ) (hk : 8 ≤ k) (hnk : 2*n ≤ k) :
    (6/7 : ℝ)^4 ≤ (((k : ℝ)-2)/((k : ℝ)-1))^n := by
  have hK : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hK1 : 0 < (k : ℝ)-1 := by linarith
  have hK2 : 0 < (k : ℝ)-2 := by linarith
  have hr0 : 0 ≤ ((k : ℝ)-2)/((k : ℝ)-1) := by positivity
  have hr1 : ((k : ℝ)-2)/((k : ℝ)-1) ≤ 1 := by
    apply (div_le_one hK1).2; linarith
  by_cases hk12 : 12 ≤ k
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hK1 hK2)
    rw [Real.log_div hK1.ne' hK2.ne'] at hlog
    have hlogratio : -(1/((k : ℝ)-2)) ≤
        Real.log (((k : ℝ)-2)/((k : ℝ)-1)) := by
      rw [Real.log_div hK2.ne' hK1.ne']
      have he : ((k : ℝ)-1)/((k : ℝ)-2)-1 = 1/((k : ℝ)-2) := by
        field_simp; ring
      rw [he] at hlog
      linarith only [hlog]
    have hN : 2*(n : ℝ) ≤ k := by exact_mod_cast hnk
    have h12 : (12 : ℝ) ≤ k := by exact_mod_cast hk12
    have hquot : (n : ℝ)/((k : ℝ)-2) ≤ 3/5 := by
      apply (div_le_iff₀ hK2).2
      linarith only [hN, h12]
    have hmul := mul_le_mul_of_nonneg_left hlogratio (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hlogpow : -(3/5 : ℝ) ≤
        Real.log ((((k : ℝ)-2)/((k : ℝ)-1))^n) := by
      rw [Real.log_pow]
      have he : (n : ℝ)* -(1/((k : ℝ)-2)) = -((n : ℝ)/((k : ℝ)-2)) := by ring
      rw [he] at hmul
      linarith only [hmul, hquot]
    have hcert := certify_log_bounds (7/6 : ℝ) 0 (3/20 : ℝ) (1/6 : ℝ)
      (by norm_num)
      (by norm_num [logSeriesLower, Finset.sum_range_succ])
      (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
    have hlogsmall : Real.log ((6/7 : ℝ)^4) ≤ -(3/5 : ℝ) := by
      rw [Real.log_pow]
      have hinv : Real.log (6/7 : ℝ) = -Real.log (7/6 : ℝ) := by
        rw [show (6/7 : ℝ) = (7/6 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hinv]
      norm_num only
      linarith only [hcert.1]
    exact (Real.log_le_log_iff (by norm_num : (0 : ℝ) < (6/7)^4)
      (pow_pos (div_pos hK2 hK1) n)).1 (hlogsmall.trans hlogpow)
  · have hk11 : k ≤ 11 := by omega
    interval_cases k
    all_goals
      have hn : n ≤ 5 := by omega
      interval_cases n <;> norm_num at *

theorem retreat_area_gain_two (k n : ℕ) (hk : 8 ≤ k) (hnk : 2*n ≤ k) :
    retreatGain * referenceArea k n ≤ retreatArea k n 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : 0 < (k : ℝ)-1 := by
    have : (8 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hratio := retreat_ratio_lower k n hk hnk
  simp only [div_pow] at hratio
  have hcross := (le_div_iff₀ (pow_pos hk1 n)).1 hratio
  unfold retreatGain referenceArea retreatArea
  rw [retreatHeight_two k hk]
  have hden : 0 < (k : ℝ)^3 := by positivity
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have hh := mul_le_mul_of_nonneg_right hcross (show 0 ≤ 16/(9*(k : ℝ)^3) by positivity)
  convert hh using 1 <;> ring

theorem exists_optimal_trim (k n : ℕ) (hk : 8 ≤ k) :
    ∃ t : ℕ, 1 ≤ t ∧ 2*t ≤ k ∧
      ∀ u : ℕ, 1 ≤ u → 2*u ≤ k → retreatArea k n u ≤ retreatArea k n t := by
  classical
  have hne : (Finset.Icc 1 (k/2)).Nonempty := ⟨2, by simp; omega⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image
    (Finset.Icc 1 (k/2)) (retreatArea k n) hne
  have htm := Finset.mem_Icc.mp ht
  refine ⟨t, htm.1, by omega, ?_⟩
  intro u hu huk
  exact hmax u (Finset.mem_Icc.mpr ⟨hu, by omega⟩)

/-- The least maximizing integer, including the specified tie rule. -/
def optimalTrim (k n : ℕ) (hk : 8 ≤ k) : ℕ :=
  by
    classical
    exact Nat.find (exists_optimal_trim k n hk)

theorem optimalTrim_spec (k n : ℕ) (hk : 8 ≤ k) :
    1 ≤ optimalTrim k n hk ∧ 2*optimalTrim k n hk ≤ k ∧
      ∀ u : ℕ, 1 ≤ u → 2*u ≤ k →
        retreatArea k n u ≤ retreatArea k n (optimalTrim k n hk) :=
  by
    classical
    exact Nat.find_spec (exists_optimal_trim k n hk)

theorem optimalTrim_gain (k n : ℕ) (hk : 8 ≤ k) (hnk : 2*n ≤ k) :
    retreatGain * referenceArea k n ≤ retreatArea k n (optimalTrim k n hk) :=
  (retreat_area_gain_two k n hk hnk).trans
    ((optimalTrim_spec k n hk).2.2 2 (by omega) (by omega))

#print axioms optimalTrim_gain
end
end Erdos953Lower
