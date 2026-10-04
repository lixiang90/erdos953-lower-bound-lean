import Erdos953Lower.AnisotropicUniform
import Erdos953Lower.RetreatGain

namespace Erdos953Lower
noncomputable section
set_option maxHeartbeats 1000000

def generationCapacity (j : ℕ) : ℝ := (4 : ℝ)^j/16
def generationRadius (j : ℕ) : ℝ := (4 : ℝ)^(j+1)

structure RetreatParameters (j : ℕ) where
  n : ℕ
  k : ℕ
  hn : 2 ≤ n
  hnk : 2*n ≤ k
  fit : (k : ℝ)^(2*n) ≤ generationCapacity j
  root : generationCapacity j < (k+1 : ℝ)^(2*n)
  next : generationCapacity j < (2*(n+1) : ℝ)^(2*(n+1))

theorem generationCapacity_ge (j : ℕ) (hj : 6 ≤ j) : 256 ≤ generationCapacity j := by
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj
  unfold generationCapacity
  norm_num at hp ⊢
  linarith only [hp]

def chosenParameters (j : ℕ) (hj : 6 ≤ j) : RetreatParameters j := by
  classical
  let h := choose_anisotropic_parameters (generationCapacity j) (generationCapacity_ge j hj)
  let n := Classical.choose h
  let k := Classical.choose (Classical.choose_spec h)
  have hs := Classical.choose_spec (Classical.choose_spec h)
  exact ⟨n,k,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2⟩

theorem retreat_parameter_n_eq {j : ℕ} (P : RetreatParameters j) (N : ℕ)
    (hN : 2 ≤ N) (hlo : (2*N : ℝ)^(2*N) ≤ generationCapacity j)
    (hhi : generationCapacity j < (2*(N+1) : ℝ)^(2*(N+1))) : P.n = N := by
  have hn := P.hn
  have hnk := P.hnk
  have hle : P.n ≤ N := by
    by_contra! h
    have hbase : (2*(N+1) : ℝ) ≤ P.k := by exact_mod_cast (by omega : 2*(N+1) ≤ P.k)
    have hpow1 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*(N+1)) hbase (2*(N+1))
    have hpow2 := pow_le_pow_right₀
      (by exact_mod_cast (by omega : 1 ≤ P.k) : (1 : ℝ) ≤ P.k)
      (by omega : 2*(N+1) ≤ 2*P.n)
    exact (not_le_of_gt hhi) (hpow1.trans (hpow2.trans P.fit))
  have hge : N ≤ P.n := by
    by_contra! h
    have hbase : (2*(P.n+1) : ℝ) ≤ 2*N := by exact_mod_cast (by omega : 2*(P.n+1) ≤ 2*N)
    have hpow1 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*(P.n+1)) hbase (2*(P.n+1))
    have hpow2 := pow_le_pow_right₀
      (by exact_mod_cast (by omega : 1 ≤ 2*N) : (1 : ℝ) ≤ 2*N)
      (by omega : 2*(P.n+1) ≤ 2*N)
    exact (not_le_of_gt P.next) (hpow1.trans (hpow2.trans hlo))
  omega

theorem retreat_parameter_k_eq {j : ℕ} (P : RetreatParameters j) (K : ℕ)
    (hlo : (K : ℝ)^(2*P.n) ≤ generationCapacity j)
    (hhi : generationCapacity j < (K+1 : ℝ)^(2*P.n)) : P.k = K := by
  have hle : P.k ≤ K := by
    by_contra! h
    have hbase : (K+1 : ℝ) ≤ P.k := by exact_mod_cast h
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ K+1) hbase (2*P.n)
    exact (not_le_of_gt hhi) (hh.trans P.fit)
  have hge : K ≤ P.k := by
    by_contra! h
    have hbase : (P.k+1 : ℝ) ≤ K := by exact_mod_cast h
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ P.k+1) hbase (2*P.n)
    exact (not_le_of_gt P.root) (hh.trans hlo)
  omega

theorem retreat_parameter_n_lower {j : ℕ} (P : RetreatParameters j) (N : ℕ)
    (hN : 2 ≤ N) (hlo : (2*N : ℝ)^(2*N) ≤ generationCapacity j) : N ≤ P.n := by
  by_contra! h
  have hbase : (2*(P.n+1) : ℝ) ≤ 2*N := by exact_mod_cast (by omega : 2*(P.n+1) ≤ 2*N)
  have hp1 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*(P.n+1)) hbase (2*(P.n+1))
  have hp2 := pow_le_pow_right₀
    (by exact_mod_cast (by omega : 1 ≤ 2*N) : (1 : ℝ) ≤ 2*N)
    (by omega : 2*(P.n+1) ≤ 2*N)
  exact (not_le_of_gt P.next) (hp1.trans (hp2.trans hlo))

theorem retreat_parameter_k_ge_eight {j : ℕ} (P : RetreatParameters j) (hj : 14 ≤ j) :
    8 ≤ P.k := by
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj
  have hlo : (8 : ℝ)^8 ≤ generationCapacity j := by
    unfold generationCapacity
    norm_num at hp ⊢
    linarith only [hp]
  have hn := retreat_parameter_n_lower P 4 (by omega) (by norm_num at hlo ⊢; exact hlo)
  have hnk := P.hnk
  omega

theorem retreat_parameter_n_ge_six {j : ℕ} (P : RetreatParameters j) (hj : 24 ≤ j) :
    6 ≤ P.n := by
  apply retreat_parameter_n_lower P 6 (by omega)
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj
  unfold generationCapacity
  norm_num at hp ⊢
  linarith only [hp]

theorem retreat_log_three : (109/100 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 9/8 := by
  exact certify_log_bounds 3 1 (109/100 : ℝ) (9/8 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower,Finset.sum_range_succ])
    (by norm_num [logSeriesUpper,logSeriesLower,Finset.sum_range_succ])

theorem retreat_log_two : (27/40 : ℝ) ≤ Real.log 2 := by
  exact (certify_log_bounds 2 1 (27/40 : ℝ) (7/10 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower,Finset.sum_range_succ])
    (by norm_num [logSeriesUpper,logSeriesLower,Finset.sum_range_succ])).1

theorem retreat_log_le_quarter (T : ℝ) (hT : 9 ≤ T) : Real.log T ≤ T/4 := by
  have ht0 : 0 < T := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num : (0 : ℝ) < 9))
  rw [Real.log_div ht0.ne' (by norm_num : (9 : ℝ) ≠ 0),
    show (9 : ℝ) = 3^2 by norm_num,Real.log_pow] at hh
  norm_num only at hh
  linarith only [hh,retreat_log_three.2,hT]

theorem retreat_log_le_eighth (T : ℝ) (hT : 27 ≤ T) : Real.log T ≤ T/8 := by
  have ht0 : 0 < T := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num : (0 : ℝ) < 27))
  rw [Real.log_div ht0.ne' (by norm_num : (27 : ℝ) ≠ 0),
    show (27 : ℝ) = 3^3 by norm_num,Real.log_pow] at hh
  norm_num only at hh
  linarith only [hh,retreat_log_three.2,hT]

end
end Erdos953Lower
