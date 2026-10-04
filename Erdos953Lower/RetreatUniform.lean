import Erdos953Lower.RetreatParameters

namespace Erdos953Lower
noncomputable section
set_option maxHeartbeats 1000000

def radiusQuotient (R : ℝ) : ℝ := Real.log (Real.log R)/Real.log R
def retreatLower (R : ℝ) : ℝ := (9/9604)*Real.sqrt R*(radiusQuotient R)^3
def earlyQuotient (j : ℕ) : ℝ := if j ≤ 12 then 1/4 else if j ≤ 18 then 1/6 else 1/8

theorem generation_log_radius (j : ℕ) (R : ℝ) (hR : generationRadius j ≤ R) :
    (2*(j+1) : ℝ)*Real.log 2 ≤ Real.log R := by
  have hh := Real.log_le_log (by unfold generationRadius; positivity) hR
  unfold generationRadius at hh
  rw [show (4 : ℝ) = 2^2 by norm_num,← pow_mul,Real.log_pow] at hh
  push_cast at hh
  nlinarith only [hh]

theorem early_radius_quotient (j : ℕ) (hj : 6 ≤ j) (R : ℝ)
    (hR : generationRadius j ≤ R) : radiusQuotient R ≤ earlyQuotient j := by
  have hlog := generation_log_radius j R hR
  have hjr : (6 : ℝ) ≤ j := by exact_mod_cast hj
  have hloglower := mul_le_mul_of_nonneg_left retreat_log_two
    (show 0 ≤ (2*(j+1) : ℝ) by positivity)
  have hT : 9 ≤ Real.log R := by nlinarith only [hlog,hloglower,hjr]
  have ht0 : 0 < Real.log R := by linarith
  unfold radiusQuotient earlyQuotient
  split_ifs with h12 h18
  · apply (div_le_iff₀ ht0).2
    nlinarith only [retreat_log_le_quarter _ hT]
  · have hj13 : (13 : ℝ) ≤ j := by exact_mod_cast (by omega : 13 ≤ j)
    have hT18 : 18 ≤ Real.log R := by nlinarith only [hlog,hloglower,hj13]
    apply (div_le_iff₀ ht0).2
    nlinarith only [log_le_one_sixth _ hT18]
  · have hj19 : (19 : ℝ) ≤ j := by exact_mod_cast (by omega : 19 ≤ j)
    have hT27 : 27 ≤ Real.log R := by nlinarith only [hlog,hloglower,hj19]
    apply (div_le_iff₀ ht0).2
    nlinarith only [retreat_log_le_eighth _ hT27]

theorem retreat_large_base_bound {j : ℕ} (P : RetreatParameters j) (hj : 24 ≤ j)
    (R : ℝ) (hR : generationRadius j ≤ R) :
    (P.k : ℝ) < 2*Real.log R/Real.log (Real.log R) := by
  have hn6 := retreat_parameter_n_ge_six P hj
  have hnk := P.hnk
  have hn2 := P.hn
  have hk0 : (0 : ℝ) < P.k := by exact_mod_cast (by omega : 0 < P.k)
  have hcap0 : 0 < generationCapacity j := by unfold generationCapacity; positivity
  have h64 : 64*generationCapacity j ≤ R := by
    unfold generationRadius at hR
    unfold generationCapacity
    rw [pow_succ] at hR
    linarith only [hR]
  have hfitR : 10*(P.k : ℝ)^(2*P.n) ≤ R := by nlinarith only [P.fit,h64,hcap0]
  have hbudget := Real.log_le_log (by positivity : 0 < 10*(P.k : ℝ)^(2*P.n)) hfitR
  rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) (pow_pos hk0 _).ne',Real.log_pow] at hbudget
  push_cast at hbudget
  have hlog := generation_log_radius j R hR
  have hlower := mul_le_mul_of_nonneg_left retreat_log_two
    (show 0 ≤ (2*(j+1) : ℝ) by positivity)
  have hjr : (24 : ℝ) ≤ j := by exact_mod_cast hj
  have hT : 6 < Real.log R := by nlinarith only [hlog,hlower,hjr]
  have hn0 : (0 : ℝ) < 2*P.n := by exact_mod_cast (by omega : 0 < 2*P.n)
  have htwopow : (2*P.n : ℝ)^(2*P.n) ≤ generationCapacity j :=
    (pow_le_pow_left₀ hn0.le (by exact_mod_cast hnk) (2*P.n)).trans P.fit
  have htwopowR : (2*P.n : ℝ)^(2*P.n) < R := by nlinarith only [htwopow,h64,hcap0]
  have hlength := Real.log_lt_log (pow_pos hn0 _) htwopowR
  rw [Real.log_pow] at hlength
  push_cast at hlength
  by_cases hn15 : P.n ≤ 15
  · exact finite_parameter_base_bound (Real.log R) (generationCapacity j) P.n P.k
      hn6 hn15 hnk P.fit P.next hbudget
  · exact large_parameter_base_bound (Real.log R) (generationCapacity j) P.n P.k
      (by omega) hT P.fit P.next hlength

def earlyK (j : ℕ) : ℕ :=
  match j with
  | 6 => 4
  | 7 => 5
  | 8 => 8
  | 9 => 11
  | 10 => 6
  | 11 => 8
  | 12 => 10
  | 13 => 12
  | 14 => 8
  | 15 => 9
  | 16 => 11
  | 17 => 13
  | 18 => 16
  | 19 => 10
  | 20 => 12
  | 21 => 13
  | 22 => 16
  | 23 => 18
  | _ => 0

def earlyN (j : ℕ) : ℕ :=
  if j ≤ 9 then 2 else if j ≤ 13 then 3 else if j ≤ 18 then 4 else 5

theorem early_parameters {j : ℕ} (P : RetreatParameters j) (hj : 6 ≤ j) (hj23 : j ≤ 23) :
    P.n = earlyN j ∧ P.k = earlyK j := by
  interval_cases j
  · have hn : P.n = 2 := retreat_parameter_n_eq P 2 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 4 := retreat_parameter_k_eq P 4
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 2 := retreat_parameter_n_eq P 2 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 5 := retreat_parameter_k_eq P 5
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 2 := retreat_parameter_n_eq P 2 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 8 := retreat_parameter_k_eq P 8
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 2 := retreat_parameter_n_eq P 2 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 11 := retreat_parameter_k_eq P 11
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 3 := retreat_parameter_n_eq P 3 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 6 := retreat_parameter_k_eq P 6
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 3 := retreat_parameter_n_eq P 3 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 8 := retreat_parameter_k_eq P 8
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 3 := retreat_parameter_n_eq P 3 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 10 := retreat_parameter_k_eq P 10
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 3 := retreat_parameter_n_eq P 3 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 12 := retreat_parameter_k_eq P 12
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 4 := retreat_parameter_n_eq P 4 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 8 := retreat_parameter_k_eq P 8
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 4 := retreat_parameter_n_eq P 4 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 9 := retreat_parameter_k_eq P 9
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 4 := retreat_parameter_n_eq P 4 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 11 := retreat_parameter_k_eq P 11
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 4 := retreat_parameter_n_eq P 4 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 13 := retreat_parameter_k_eq P 13
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 4 := retreat_parameter_n_eq P 4 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 16 := retreat_parameter_k_eq P 16
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 5 := retreat_parameter_n_eq P 5 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 10 := retreat_parameter_k_eq P 10
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 5 := retreat_parameter_n_eq P 5 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 12 := retreat_parameter_k_eq P 12
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 5 := retreat_parameter_n_eq P 5 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 13 := retreat_parameter_k_eq P 13
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 5 := retreat_parameter_n_eq P 5 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 16 := retreat_parameter_k_eq P 16
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩
  · have hn : P.n = 5 := retreat_parameter_n_eq P 5 (by norm_num)
      (by norm_num [generationCapacity]) (by norm_num [generationCapacity])
    have hk : P.k = 18 := retreat_parameter_k_eq P 18
      (by norm_num [hn,generationCapacity]) (by norm_num [hn,generationCapacity])
    exact ⟨by simpa [earlyN] using hn, by simpa [earlyK] using hk⟩

theorem early_reference_area {j : ℕ} (P : RetreatParameters j) (hj : 6 ≤ j) (hj23 : j ≤ 23) :
    (2 : ℝ)^(j+2)*(earlyQuotient j)^3 < 55296*referenceArea P.k P.n := by
  obtain ⟨hn,hk⟩ := early_parameters P hj hj23
  rw [hn,hk]
  interval_cases j <;> norm_num [earlyK,earlyN,earlyQuotient,referenceArea]

theorem early_prefix_area {j : ℕ} (P : RetreatParameters j) (hj : 6 ≤ j) (hj13 : j ≤ 13) :
    retreatGain*referenceArea P.k P.n ≤ 3/8 := by
  obtain ⟨hn,hk⟩ := early_parameters P hj (by omega)
  rw [hn,hk]
  interval_cases j <;> norm_num [earlyK,earlyN,referenceArea,retreatGain]

theorem complete_generation_for_radius (R : ℝ) (hR : 16384 ≤ R) :
    ∃ j : ℕ, 6 ≤ j ∧ generationRadius j ≤ R ∧ R < generationRadius (j+1) := by
  obtain ⟨m,hm,hnext⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ R by linarith) (by norm_num : (1 : ℝ) < 4)
  have hm7 : 7 ≤ m := by
    by_contra! h
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (show m+1 ≤ 7 by omega)
    norm_num at hp
    linarith only [hnext,hp,hR]
  refine ⟨m-1,by omega,?_,?_⟩
  · simpa [generationRadius,show m-1+1=m by omega] using hm
  · simpa [generationRadius,show m-1+1+1=m+1 by omega] using hnext

theorem complete_generation_sqrt_upper (j : ℕ) (R : ℝ)
    (hR : R < generationRadius (j+1)) : Real.sqrt R < (2 : ℝ)^(j+2) := by
  have hp : ((2 : ℝ)^(j+2))^2 = (4 : ℝ)^(j+2) := by
    rw [show (4 : ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul]
    congr 1
    omega
  have hs0 := Real.sqrt_nonneg R
  have hp0 : 0 < (2 : ℝ)^(j+2) := by positivity
  unfold generationRadius at hR
  have hsq : R < ((2 : ℝ)^(j+2))^2 := by simpa only [hp,Nat.add_assoc] using hR
  by_cases hr0 : 0 ≤ R
  · have hsr := Real.sq_sqrt hr0
    nlinarith only [hsr,hs0,hp0,hsq]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hr0)]
    exact hp0

theorem reference_area_for_real_radius {j : ℕ} (P : RetreatParameters j) (hj : 6 ≤ j)
    (R : ℝ) (hR : generationRadius j ≤ R) (hnext : R < generationRadius (j+1)) :
    Real.sqrt R*(radiusQuotient R)^3/55296 ≤ referenceArea P.k P.n := by
  have hlog := generation_log_radius j R hR
  have hlower := mul_le_mul_of_nonneg_left retreat_log_two (show 0 ≤ (2*(j+1) : ℝ) by positivity)
  have hjr : (6 : ℝ) ≤ j := by exact_mod_cast hj
  have hT : 9 ≤ Real.log R := by nlinarith only [hlog,hlower,hjr]
  have ht0 : 0 < Real.log R := by linarith
  have hz0 : 0 < Real.log (Real.log R) := Real.log_pos (by linarith : 1 < Real.log R)
  have hq0 : 0 ≤ radiusQuotient R := by unfold radiusQuotient; positivity
  have hR0 : 0 < R := (by unfold generationRadius; positivity : 0 < generationRadius j).trans_le hR
  have hs0 : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hsqrt := complete_generation_sqrt_upper j R hnext
  by_cases hj23 : j ≤ 23
  · have hq := early_radius_quotient j hj R hR
    have hqpow := pow_le_pow_left₀ hq0 hq 3
    have hprod := mul_le_mul hsqrt.le hqpow (pow_nonneg hq0 3) (by positivity : (0 : ℝ) ≤ 2^(j+2))
    have hcert := early_reference_area P hj hj23
    linarith only [hprod,hcert]
  · have hj24 : 24 ≤ j := by omega
    have hnk := P.hnk
    have hn := P.hn
    have hk0 : (0 : ℝ) < P.k := by exact_mod_cast (by omega : 0 < P.k)
    have hC0 : 0 ≤ generationCapacity j := by unfold generationCapacity; positivity
    have hcount := anisotropic_digit_count_lower (generationCapacity j) P.k P.n hC0
      (by exact_mod_cast (by omega : 1 ≤ P.k)) (by exact_mod_cast hnk) P.root
    have hcap : Real.sqrt (generationCapacity j) = (2 : ℝ)^j/4 := by
      have he : (4 : ℝ)^j = ((2 : ℝ)^j)^2 := by
        rw [show (4 : ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul]
        congr 1; omega
      have hh : (Real.sqrt (generationCapacity j))^2 = ((2 : ℝ)^j)^2/16 := by
        rw [Real.sq_sqrt hC0]
        unfold generationCapacity
        rw [he]
      have hh0 := Real.sqrt_nonneg (generationCapacity j)
      have hp0 : 0 < (2 : ℝ)^j := by positivity
      nlinarith only [hh,hh0,hp0]
    rw [hcap] at hcount
    have hs : Real.sqrt R < 64*((P.k : ℝ)-1)^P.n := by
      rw [show (2 : ℝ)^(j+2) = 4*(2 : ℝ)^j by rw [pow_add]; ring] at hsqrt
      linarith only [hsqrt,hcount]
    have hkbound := retreat_large_base_bound P hj24 R hR
    have hkq : (P.k : ℝ)*radiusQuotient R < 2 := by
      have hh := (lt_div_iff₀ hz0).1 hkbound
      unfold radiusQuotient
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ ht0).2
      nlinarith only [hh]
    have hkq3 : ((P.k : ℝ)*radiusQuotient R)^3 < (2 : ℝ)^3 := by
      gcongr
    have hprod := mul_lt_mul_of_pos_left hkq3 hs0
    unfold referenceArea
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 108*(P.k : ℝ)^3)).2
    nlinarith only [hprod,hs]

theorem retreatLower_for_generation {j : ℕ} (P : RetreatParameters j) (hj : 6 ≤ j)
    (R : ℝ) (hR : generationRadius j ≤ R) (hnext : R < generationRadius (j+1)) :
    retreatLower R ≤ retreatGain*referenceArea P.k P.n := by
  have hh := mul_le_mul_of_nonneg_left (reference_area_for_real_radius P hj R hR hnext)
    (show 0 ≤ retreatGain by norm_num [retreatGain])
  unfold retreatLower retreatGain at *
  nlinarith only [hh]

#print axioms retreatLower_for_generation
#print axioms early_reference_area
#print axioms early_prefix_area

end
end Erdos953Lower
