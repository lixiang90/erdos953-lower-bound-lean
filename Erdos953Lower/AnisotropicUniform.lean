import Erdos953Lower.AnisotropicRectangles
import Erdos953Lower.AnisotropicLogCertificates
import Mathlib.Analysis.Real.Pi.Bounds

namespace Erdos953Lower
noncomputable section
set_option maxHeartbeats 400000

theorem log_radius_ge_eighteen (R : ℝ) (hR : 1000000000 ≤ R) :
    18 ≤ Real.log R := by
  have hlog3 : 1 ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three.le
  have hpow : (3 : ℝ) ^ 18 ≤ R := by norm_num at *; linarith only [hR]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ 18) hpow
  rw [Real.log_pow] at hlog
  norm_num only at hlog
  linarith only [hlog, hlog3]

theorem log_le_one_sixth (T : ℝ) (hT : 18 ≤ T) : Real.log T ≤ T / 6 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hlog83 : Real.log (8 / 3 : ℝ) < 1 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 8 / 3)).2
    linarith only [Real.exp_one_gt_d9]
  have hlog18 : Real.log 18 ≤ 3 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 18)
      (by norm_num : (18 : ℝ) ≤ (8 / 3) ^ 3)
    rw [Real.log_pow] at h
    norm_num only at h
    linarith only [h, hlog83]
  have htan := Real.log_le_sub_one_of_pos (div_pos hT0 (by norm_num : (0 : ℝ) < 18))
  rw [Real.log_div hT0.ne' (by norm_num : (18 : ℝ) ≠ 0)] at htan
  linarith only [htan, hlog18, hT]

theorem large_parameter_base_bound (T A : ℝ) (n k : ℕ)
    (hn : 16 ≤ n) (hT : 6 < T)
    (hfit : (k : ℝ) ^ (2 * n) ≤ A)
    (hnext : A < (2 * (n + 1) : ℝ) ^ (2 * (n + 1)))
    (hbudget : (2 * n : ℝ) * Real.log (2 * n : ℝ) < T) :
    (k : ℝ) < 2 * T / Real.log T := by
  let B : ℝ := 2 * (n + 1)
  let C : ℝ := (5 / 2) * (n + 1)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hB := next_base_le_geometric n hn
  have hpow83 : ((5 / 4 : ℝ) ^ n) ^ 2 = (5 / 4 : ℝ) ^ (2 * n) := by
    rw [← pow_mul]
    congr 1
    omega
  have hnextle : B ^ (2 * (n + 1)) ≤ C ^ (2 * n) := by
    calc
      B ^ (2 * (n + 1)) = B ^ (2 * n) * B ^ 2 := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      _ ≤ B ^ (2 * n) * (((5 / 4 : ℝ) ^ n) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hB 2) (pow_nonneg hB0 _)
      _ = (B * (5 / 4 : ℝ)) ^ (2 * n) := by
        rw [hpow83]
        exact (mul_pow B (5 / 4 : ℝ) (2 * n)).symm
      _ = C ^ (2 * n) := by congr 1; dsimp [B, C]; ring
  have hkC : (k : ℝ) < C := by
    by_contra! h
    have hpow := pow_le_pow_left₀ hC0 h (2 * n)
    have hbad := hnextle.trans (hpow.trans hfit)
    exact (not_le_of_gt hnext) hbad
  have hlength := anisotropic_length_bound T n hT (by omega) hbudget
  have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hC : C ≤ (8 / 3 : ℝ) * n := by dsimp [C]; linarith only [hn']
  calc
    (k : ℝ) < C := hkC
    _ ≤ (8 / 3 : ℝ) * n := hC
    _ < (8 / 3 : ℝ) * (3 * T / (4 * Real.log T)) :=
      mul_lt_mul_of_pos_left hlength (by norm_num)
    _ = 2 * T / Real.log T := by ring

theorem choose_uniform_anisotropic_parameters (R : ℝ) (hR : 100000000000000 ≤ R) :
    ∃ n k : ℕ, 2 ≤ n ∧ 3 ≤ k ∧ 2 * n ≤ k ∧
      (k : ℝ) ^ (2 * n) ≤ R / 10 ∧ R / 10 < (k + 1 : ℝ) ^ (2 * n) ∧
      (k : ℝ) < 2 * Real.log R / Real.log (Real.log R) := by
  have hR0 : 0 < R := by linarith only [hR]
  obtain ⟨n, k, hn2, hnk, hfit, hgrid, hnext⟩ :=
    choose_anisotropic_parameters (R / 10) (by linarith only [hR])
  have hn6 : 6 ≤ n := by
    by_contra! h
    have hbase : (2 * (n + 1) : ℝ) ≤ 12 := by exact_mod_cast (by omega : 2 * (n + 1) ≤ 12)
    have hpow1 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * (n + 1))
      hbase (2 * (n + 1))
    have hpow2 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 12)
      (by omega : 2 * (n + 1) ≤ 12)
    have hnextBound : R / 10 < (12 : ℝ) ^ 12 := hnext.trans_le (hpow1.trans hpow2)
    norm_num at hnextBound
    linarith only [hnextBound, hR]
  have hk : 3 ≤ k := by omega
  have hT : 6 < Real.log R := by
    have := log_radius_ge_eighteen R (by linarith only [hR])
    linarith only [this]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hfitR : 10 * (k : ℝ) ^ (2 * n) ≤ R := by linarith only [hfit]
  have hbudget := Real.log_le_log (by positivity : (0 : ℝ) < 10 * (k : ℝ) ^ (2 * n)) hfitR
  rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) (pow_pos hk0 _).ne', Real.log_pow] at hbudget
  have hbudget' : Real.log 10 + (2 * n : ℝ) * Real.log k ≤ Real.log R := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget
  have hn0 : (0 : ℝ) < 2 * n := by exact_mod_cast (by omega : 0 < 2 * n)
  have htwopow : (2 * n : ℝ) ^ (2 * n) ≤ R / 10 := by
    exact (pow_le_pow_left₀ hn0.le (by exact_mod_cast hnk) (2 * n)).trans hfit
  have htwopowR : (2 * n : ℝ) ^ (2 * n) < R := by linarith only [htwopow, hR0]
  have hlengthBudget := Real.log_lt_log (pow_pos hn0 _) htwopowR
  rw [Real.log_pow] at hlengthBudget
  have hlengthBudget' : (2 * n : ℝ) * Real.log (2 * n : ℝ) < Real.log R := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlengthBudget
  have hkbound : (k : ℝ) < 2 * Real.log R / Real.log (Real.log R) := by
    by_cases hn15 : n ≤ 15
    · exact finite_parameter_base_bound (Real.log R) (R / 10) n k
        hn6 hn15 hnk hfit hnext hbudget'
    · exact large_parameter_base_bound (Real.log R) (R / 10) n k
        (by omega) hT hfit hnext hlengthBudget'
  exact ⟨n, k, hn2, hk, hnk, hfit, hgrid, hkbound⟩

def sharpLower (R : ℝ) : ℝ :=
  Real.sqrt (R / 10) / 32768 * (Real.log (Real.log R) / Real.log R) ^ 3

theorem sharpLower_small_radius (R : ℝ) (hR : Real.exp 1 ≤ R)
    (hRmax : R ≤ 100000000000000) : sharpLower R ≤ Real.pi / 4 := by
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have hT1 : 1 ≤ Real.log R := (Real.le_log_iff_exp_le hR0).2 hR
  have hT0 : 0 < Real.log R := by linarith only [hT1]
  have hq0 : 0 ≤ Real.log (Real.log R) / Real.log R :=
    div_nonneg (Real.log_nonneg hT1) hT0.le
  have hq1 : Real.log (Real.log R) / Real.log R ≤ 1 := by
    apply (div_le_iff₀ hT0).2
    simpa only [one_mul] using Real.log_le_self hT0.le
  have hs0 := Real.sqrt_nonneg (R / 10)
  have hs2 := Real.sq_sqrt (show 0 ≤ R / 10 by positivity)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  unfold sharpLower
  by_cases hsmall : R ≤ 1000000000
  · have hs : Real.sqrt (R / 10) ≤ 10000 := by nlinarith only [hs0, hs2, hsmall]
    have hqpow : (Real.log (Real.log R) / Real.log R) ^ 3 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hq0 hq1 3
    have hbound := mul_le_mul hs hqpow (pow_nonneg hq0 3) (by norm_num : (0 : ℝ) ≤ 10000)
    nlinarith only [hbound, hpi]
  · have hT18 := log_radius_ge_eighteen R (le_of_not_ge hsmall)
    have hq6 : Real.log (Real.log R) / Real.log R ≤ 1 / 6 := by
      apply (div_le_iff₀ hT0).2
      nlinarith only [log_le_one_sixth (Real.log R) hT18]
    have hs : Real.sqrt (R / 10) ≤ 4000000 := by nlinarith only [hs0, hs2, hRmax]
    have hqpow := pow_le_pow_left₀ hq0 hq6 3
    have hbound := mul_le_mul hs hqpow (pow_nonneg hq0 3) (by norm_num : (0 : ℝ) ≤ 4000000)
    norm_num only at hbound
    nlinarith only [hbound, hpi]

#print axioms sharpLower_small_radius
#print axioms choose_uniform_anisotropic_parameters
end
end Erdos953Lower
