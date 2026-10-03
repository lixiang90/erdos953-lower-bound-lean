/- Generated rational certificates. Every numerical inequality is proved by
norm_num in Lean against a theorem with an explicit logarithm remainder.
Regenerate with research/generate_953_lean_log_certificates.py. -/
import Erdos953Lower.AnisotropicLogBounds
import Mathlib.Tactic.IntervalCases

namespace Erdos953Lower
noncomputable section
set_option maxHeartbeats 2000000

theorem certified_log_ten : (2301 / 1000 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ (288 / 125 : ℝ) := by
  exact certify_log_bounds 10 3 (2301 / 1000 : ℝ) (288 / 125 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])

theorem certified_base_budget_6 :
    (21 : ℝ) * Real.log (Real.log 10 + 12 * Real.log 21) <
      2 * (Real.log 10 + 12 * Real.log 21) := by
  have hk := certify_log_bounds 21 4 (3043 / 1000 : ℝ) (1523 / 500 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (38817 / 1000 : ℝ) ≤ Real.log 10 + 12 * Real.log 21 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 12 * Real.log 21 ≤ (4857 / 125 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 12 * Real.log 21 := by
    linarith only [htlo]
  have houter := certify_log_bounds (4857 / 125 : ℝ) 5 (1829 / 500 : ℝ) (3661 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 12 * Real.log 21) ≤ (3661 / 1000 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (21 : ℝ) * (3661 / 1000 : ℝ) < 2 * (38817 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem certified_base_budget_7 :
    (23 : ℝ) * Real.log (Real.log 10 + 14 * Real.log 23) <
      2 * (Real.log 10 + 14 * Real.log 23) := by
  have hk := certify_log_bounds 23 4 (1567 / 500 : ℝ) (3137 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (46177 / 1000 : ℝ) ≤ Real.log 10 + 14 * Real.log 23 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 14 * Real.log 23 ≤ (23111 / 500 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 14 * Real.log 23 := by
    linarith only [htlo]
  have houter := certify_log_bounds (23111 / 500 : ℝ) 5 (479 / 125 : ℝ) (767 / 200 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 14 * Real.log 23) ≤ (767 / 200 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (23 : ℝ) * (767 / 200 : ℝ) < 2 * (46177 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem certified_base_budget_8 :
    (25 : ℝ) * Real.log (Real.log 10 + 16 * Real.log 25) <
      2 * (Real.log 10 + 16 * Real.log 25) := by
  have hk := certify_log_bounds 25 4 (3217 / 1000 : ℝ) (161 / 50 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (53773 / 1000 : ℝ) ≤ Real.log 10 + 16 * Real.log 25 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 16 * Real.log 25 ≤ (6728 / 125 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 16 * Real.log 25 := by
    linarith only [htlo]
  have houter := certify_log_bounds (6728 / 125 : ℝ) 5 (498 / 125 : ℝ) (3987 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 16 * Real.log 25) ≤ (3987 / 1000 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (25 : ℝ) * (3987 / 1000 : ℝ) < 2 * (53773 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem certified_base_budget_9 :
    (27 : ℝ) * Real.log (Real.log 10 + 18 * Real.log 27) <
      2 * (Real.log 10 + 18 * Real.log 27) := by
  have hk := certify_log_bounds 27 4 (1647 / 500 : ℝ) (3297 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (61593 / 1000 : ℝ) ≤ Real.log 10 + 18 * Real.log 27 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 18 * Real.log 27 ≤ (1233 / 20 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 18 * Real.log 27 := by
    linarith only [htlo]
  have houter := certify_log_bounds (1233 / 20 : ℝ) 5 (103 / 25 : ℝ) (4123 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 18 * Real.log 27) ≤ (4123 / 1000 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (27 : ℝ) * (4123 / 1000 : ℝ) < 2 * (61593 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem certified_base_budget_10 :
    (29 : ℝ) * Real.log (Real.log 10 + 20 * Real.log 29) <
      2 * (Real.log 10 + 20 * Real.log 29) := by
  have hk := certify_log_bounds 29 4 (1683 / 500 : ℝ) (3369 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (69621 / 1000 : ℝ) ≤ Real.log 10 + 20 * Real.log 29 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 20 * Real.log 29 ≤ (17421 / 250 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 20 * Real.log 29 := by
    linarith only [htlo]
  have houter := certify_log_bounds (17421 / 250 : ℝ) 6 (2121 / 500 : ℝ) (849 / 200 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 20 * Real.log 29) ≤ (849 / 200 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (29 : ℝ) * (849 / 200 : ℝ) < 2 * (69621 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem certified_base_budget_11 :
    (32 : ℝ) * Real.log (Real.log 10 + 22 * Real.log 32) <
      2 * (Real.log 10 + 22 * Real.log 32) := by
  have hk := certify_log_bounds 32 5 (433 / 125 : ℝ) (3467 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (78509 / 1000 : ℝ) ≤ Real.log 10 + 22 * Real.log 32 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 22 * Real.log 32 ≤ (39289 / 500 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 22 * Real.log 32 := by
    linarith only [htlo]
  have houter := certify_log_bounds (39289 / 500 : ℝ) 6 (4363 / 1000 : ℝ) (2183 / 500 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 22 * Real.log 32) ≤ (2183 / 500 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (32 : ℝ) * (2183 / 500 : ℝ) < 2 * (78509 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem certified_base_budget_12 :
    (34 : ℝ) * Real.log (Real.log 10 + 24 * Real.log 34) <
      2 * (Real.log 10 + 24 * Real.log 34) := by
  have hk := certify_log_bounds 34 5 (141 / 40 : ℝ) (441 / 125 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (86901 / 1000 : ℝ) ≤ Real.log 10 + 24 * Real.log 34 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 24 * Real.log 34 ≤ (10872 / 125 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 24 * Real.log 34 := by
    linarith only [htlo]
  have houter := certify_log_bounds (10872 / 125 : ℝ) 6 (558 / 125 : ℝ) (4467 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 24 * Real.log 34) ≤ (4467 / 1000 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (34 : ℝ) * (4467 / 1000 : ℝ) < 2 * (86901 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem certified_base_budget_13 :
    (36 : ℝ) * Real.log (Real.log 10 + 26 * Real.log 36) <
      2 * (Real.log 10 + 26 * Real.log 36) := by
  have hk := certify_log_bounds 36 5 (1791 / 500 : ℝ) (717 / 200 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (95433 / 1000 : ℝ) ≤ Real.log 10 + 26 * Real.log 36 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 26 * Real.log 36 ≤ (47757 / 500 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 26 * Real.log 36 := by
    linarith only [htlo]
  have houter := certify_log_bounds (47757 / 500 : ℝ) 6 (2279 / 500 : ℝ) (4561 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 26 * Real.log 36) ≤ (4561 / 1000 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (36 : ℝ) * (4561 / 1000 : ℝ) < 2 * (95433 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem certified_base_budget_14 :
    (38 : ℝ) * Real.log (Real.log 10 + 28 * Real.log 38) <
      2 * (Real.log 10 + 28 * Real.log 38) := by
  have hk := certify_log_bounds 38 5 (909 / 250 : ℝ) (3639 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (104109 / 1000 : ℝ) ≤ Real.log 10 + 28 * Real.log 38 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 28 * Real.log 38 ≤ (26049 / 250 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 28 * Real.log 38 := by
    linarith only [htlo]
  have houter := certify_log_bounds (26049 / 250 : ℝ) 6 (929 / 200 : ℝ) (581 / 125 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 28 * Real.log 38) ≤ (581 / 125 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (38 : ℝ) * (581 / 125 : ℝ) < 2 * (104109 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem certified_base_budget_15 :
    (40 : ℝ) * Real.log (Real.log 10 + 30 * Real.log 40) <
      2 * (Real.log 10 + 30 * Real.log 40) := by
  have hk := certify_log_bounds 40 5 (3687 / 1000 : ℝ) (369 / 100 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have htlo : (112911 / 1000 : ℝ) ≤ Real.log 10 + 30 * Real.log 40 := by
    linarith only [certified_log_ten.1, hk.1]
  have hthi : Real.log 10 + 30 * Real.log 40 ≤ (28251 / 250 : ℝ) := by
    linarith only [certified_log_ten.2, hk.2]
  have htpos : 0 < Real.log 10 + 30 * Real.log 40 := by
    linarith only [htlo]
  have houter := certify_log_bounds (28251 / 250 : ℝ) 6 (2363 / 500 : ℝ) (4729 / 1000 : ℝ)
    (by norm_num)
    (by norm_num [logSeriesLower, Finset.sum_range_succ])
    (by norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ])
  have hlog : Real.log (Real.log 10 + 30 * Real.log 40) ≤ (4729 / 1000 : ℝ) :=
    (Real.log_le_log htpos hthi).trans houter.2
  have hnum : (40 : ℝ) * (4729 / 1000 : ℝ) < 2 * (112911 / 1000 : ℝ) := by norm_num
  linarith only [hlog, htlo, hnum]

theorem finite_max_base_certificate (n : ℕ) (hn : 6 ≤ n) (hn' : n ≤ 15) :
    ∃ K : ℕ,
      (2 * (n + 1) : ℝ) ^ (2 * (n + 1)) ≤ (K + 1 : ℝ) ^ (2 * n) ∧
      (K : ℝ) * Real.log (Real.log 10 + (2 * n : ℝ) * Real.log K) <
        2 * (Real.log 10 + (2 * n : ℝ) * Real.log K) := by
  interval_cases n
  · refine ⟨21, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_6
  · refine ⟨23, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_7
  · refine ⟨25, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_8
  · refine ⟨27, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_9
  · refine ⟨29, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_10
  · refine ⟨32, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_11
  · refine ⟨34, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_12
  · refine ⟨36, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_13
  · refine ⟨38, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_14
  · refine ⟨40, by norm_num, ?_⟩
    norm_num only
    exact certified_base_budget_15

theorem finite_parameter_base_bound (T A : ℝ) (n k : ℕ)
    (hn : 6 ≤ n) (hn' : n ≤ 15) (hnk : 2 * n ≤ k)
    (hfit : (k : ℝ) ^ (2 * n) ≤ A)
    (hnext : A < (2 * (n + 1) : ℝ) ^ (2 * (n + 1)))
    (hbudget : Real.log 10 + (2 * n : ℝ) * Real.log k ≤ T) :
    (k : ℝ) < 2 * T / Real.log T := by
  obtain ⟨K, hmax, hcert⟩ := finite_max_base_certificate n hn hn'
  have hkK : k ≤ K := by
    by_contra! h
    have hreal : (K + 1 : ℝ) ≤ k := by exact_mod_cast h
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ K + 1) hreal (2 * n)
    have hwrong := hmax.trans (hpow.trans hfit)
    exact (not_le_of_gt hnext) hwrong
  exact base_bound_from_max T n k K hn hnk hkK hbudget hcert

#print axioms finite_parameter_base_bound
end
end Erdos953Lower
