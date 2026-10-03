import Erdos953Lower.AnisotropicParameters
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos953Lower
noncomputable section
set_option maxHeartbeats 300000

theorem nat_base_le_pow (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    (m : ℝ) ≤ (m : ℝ) ^ p := by
  simpa only [pow_one] using
    (pow_le_pow_right₀ (by exact_mod_cast hm : (1 : ℝ) ≤ m) hp)

/-- Maximal digit length and integer root, for arbitrary real capacities. -/
theorem choose_anisotropic_parameters (A : ℝ) (hA : 256 ≤ A) :
    ∃ n k : ℕ, 2 ≤ n ∧ 2 * n ≤ k ∧
      (k : ℝ) ^ (2 * n) ≤ A ∧ A < (k + 1 : ℝ) ^ (2 * n) ∧
      A < (2 * (n + 1) : ℝ) ^ (2 * (n + 1)) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt A
  have hN2 : 2 ≤ N := by
    by_contra h
    have h' : (N : ℝ) ≤ 1 := by exact_mod_cast (by omega : N ≤ 1)
    linarith only [hA, hN, h']
  let P : ℕ → Prop := fun m => (2 * m : ℝ) ^ (2 * m) ≤ A
  have hP2 : P 2 := by dsimp [P]; norm_num; exact hA
  have hPN : ¬ P N := by
    have hpow : (2 * N : ℝ) ≤ (2 * N : ℝ) ^ (2 * N) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        nat_base_le_pow (2 * N) (2 * N) (by omega) (by omega)
    dsimp [P]
    intro h
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith only [hN, hpow, h, hN0]
  let n := Nat.findGreatest P N
  have hnP : P n := Nat.findGreatest_spec hN2 hP2
  have hn2 : 2 ≤ n := Nat.le_findGreatest hN2 hP2
  have hnN : n < N := by
    have hnle : n ≤ N := Nat.findGreatest_le N
    by_contra h
    have hnEq : n = N := by omega
    exact hPN (hnEq ▸ hnP)
  have hnnext : A < (2 * (n + 1) : ℝ) ^ (2 * (n + 1)) := by
    have hnot : ¬ P (n + 1) :=
      Nat.findGreatest_is_greatest (P := P) (n := N) (k := n + 1)
        (by change n < n + 1; omega) (by omega)
    simpa only [P, Nat.cast_add, Nat.cast_one] using lt_of_not_ge hnot
  have htwonpow : (2 * n : ℝ) ≤ (2 * n : ℝ) ^ (2 * n) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      nat_base_le_pow (2 * n) (2 * n) (by omega) (by omega)
  have htwonN : 2 * n ≤ N := by
    have h : (2 * n : ℝ) < N := (htwonpow.trans hnP).trans_lt hN
    exact_mod_cast h.le
  let Q : ℕ → Prop := fun m => (m : ℝ) ^ (2 * n) ≤ A
  have hQN : ¬ Q N := by
    have hpow := nat_base_le_pow N (2 * n) (by omega) (by omega)
    dsimp [Q]
    intro h
    linarith only [hpow, hN, h]
  let k := Nat.findGreatest Q N
  have hkQ : Q k := Nat.findGreatest_spec htwonN (by
    dsimp [Q]; simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnP)
  have hnk : 2 * n ≤ k := Nat.le_findGreatest htwonN (by
    dsimp [Q]; simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnP)
  have hkN : k < N := by
    have hkle : k ≤ N := Nat.findGreatest_le N
    by_contra h
    have hkEq : k = N := by omega
    exact hQN (hkEq ▸ hkQ)
  have hknext : A < (k + 1 : ℝ) ^ (2 * n) := by
    have hnot : ¬ Q (k + 1) :=
      Nat.findGreatest_is_greatest (P := Q) (n := N) (k := k + 1)
        (by change k < k + 1; omega) (by omega)
    simpa only [Q, Nat.cast_add, Nat.cast_one] using lt_of_not_ge hnot
  exact ⟨n, k, hn2, hnk, hkQ, hknext, hnnext⟩

theorem next_base_le_geometric (n : ℕ) (hn : 16 ≤ n) :
    2 * (n + 1 : ℝ) ≤ (5 / 4 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    push_cast
    have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [ih, hn']

/-- A tangent bound for log inverts the length inequality without Lambert W. -/
theorem anisotropic_length_bound (T : ℝ) (n : ℕ) (hT : 6 < T) (hn : 2 ≤ n)
    (hbudget : (2 * n : ℝ) * Real.log (2 * n : ℝ) < T) :
    (n : ℝ) < 3 * T / (4 * Real.log T) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hz : 0 < Real.log T := Real.log_pos (by linarith only [hT])
  have hlog2 : Real.log 2 < 1 := by
    exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2 Real.exp_one_gt_two
  let s : ℝ := 3 * T / (2 * Real.log T)
  have hs0 : 0 < s := by dsimp [s]; positivity
  have htangent := Real.log_le_sub_one_of_pos (div_pos hz (by norm_num : (0 : ℝ) < 3))
  rw [Real.log_div hz.ne' (by norm_num : (3 : ℝ) ≠ 0)] at htangent
  have hlogs : Real.log s = Real.log 3 + Real.log T - Real.log 2 -
      Real.log (Real.log T) := by
    dsimp [s]
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) hT0.ne', Real.log_mul (by norm_num) hz.ne']
    ring
  have hlogsLower : (2 / 3 : ℝ) * Real.log T < Real.log s := by
    linarith only [htangent, hlog2, hlogs]
  have hsBudget : T < s * Real.log s := by
    have h := mul_lt_mul_of_pos_left hlogsLower hs0
    have heq : s * ((2 / 3 : ℝ) * Real.log T) = T := by
      dsimp [s]
      field_simp
    rw [heq] at h
    exact h
  have hn1 : (1 : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : 1 ≤ 2 * n)
  have hexp : Real.exp (-1) ≤ (1 : ℝ) := by
    exact (Real.exp_le_one_iff).2 (by norm_num)
  have hns : (2 * n : ℝ) < s := by
    by_contra! h
    have hmono := Real.mul_log_strictMonoOn.monotoneOn
      (show s ∈ Set.Ici (Real.exp (-1)) from
        (by
          have hsl : (1 : ℝ) ≤ s := by
            have hlogT := Real.log_le_self hT0.le
            dsimp [s]
            apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log T)).2
            linarith only [hlogT, hT0]
          exact hexp.trans hsl))
      (show (2 * n : ℝ) ∈ Set.Ici (Real.exp (-1)) from hexp.trans hn1) h
    linarith only [hmono, hbudget, hsBudget]
  dsimp [s] at hns
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.log T)).2
  have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log T)).1 hns
  linarith only [h]

#print axioms choose_anisotropic_parameters
#print axioms anisotropic_length_bound
end
end Erdos953Lower
