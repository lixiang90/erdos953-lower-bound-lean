/-
  Erdős Problem 953: radius bounds for the finite digit point sets.
-/
import Erdos953Lower.DigitPoints
import Erdos953Lower.DigitTail
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

namespace Erdos953Lower

open Finset

lemma digitAt_nonneg (k n : ℕ) (α : Fin n → Fin (k - 1)) (j : ℕ) :
    0 ≤ digitAt k n α j := by
  by_cases hj : j < n
  · simp [digitAt, hj]
  · simp [digitAt, hj]

lemma digitAt_le (k n : ℕ) (hk : 3 ≤ k)
    (α : Fin n → Fin (k - 1)) (j : ℕ) :
    digitAt k n α j ≤ (k : ℤ) - 2 := by
  by_cases hj : j < n
  · have h := (α ⟨j, hj⟩).isLt
    simp only [digitAt, hj, dite_true]
    omega
  · simp [digitAt, hj]
    omega

theorem xCoord_bound (k n : ℕ) (hk : 3 ≤ k)
    (α : Fin n → Fin (k - 1)) :
    0 ≤ xCoord k n α ∧ xCoord k n α < (k : ℤ) ^ n := by
  have hK : (0 : ℤ) ≤ k := by positivity
  have hlo : 0 ≤ xCoord k n α := by
    unfold xCoord
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (digitAt_nonneg k n α j) (pow_nonneg hK j)
  have hhi : xCoord k n α ≤
      ((k : ℤ) - 2) * (∑ j ∈ range n, (k : ℤ) ^ j) := by
    unfold xCoord
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right
      (digitAt_le k n hk α j) (pow_nonneg hK j)
  exact ⟨hlo, lt_of_le_of_lt hhi (linear_digit_tail k n hk)⟩

theorem yCoord_bound (k n : ℕ) (hk : 3 ≤ k)
    (α : Fin n → Fin (k - 1)) :
    0 ≤ yCoord k n α ∧
      yCoord k n α < 4 * (k : ℤ) ^ 2 * (((k : ℤ) ^ 2) ^ n) := by
  let K : ℤ := k
  let q : ℤ := K ^ 2
  let T : ℤ := ∑ j ∈ range n, digitAt k n α j * q ^ j
  let S : ℤ := ∑ j ∈ range n, q ^ j
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hTlo : 0 ≤ T := by
    dsimp [T]
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (digitAt_nonneg k n α j) (pow_nonneg hq j)
  have hThi : T ≤ (K - 2) * S := by
    dsimp [T, S]
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right
      (digitAt_le k n hk α j) (pow_nonneg hq j)
  have htail : 2 * (K - 2) * S < q ^ n := by
    simpa [K, q, S] using quadratic_digit_tail k n hk
  have hKsq : 0 < K ^ 2 := by
    have : (3 : ℤ) ≤ K := by dsimp [K]; exact_mod_cast hk
    nlinarith
  constructor
  · change 0 ≤ 8 * K * T
    positivity
  · change 8 * K * T < 4 * K ^ 2 * q ^ n
    have hscale : 0 < 4 * K * (q ^ n - 2 * T) := by
      apply mul_pos (by positivity)
      nlinarith
    have hKleSq : K ≤ K ^ 2 := by
      have hK3 : (3 : ℤ) ≤ K := by dsimp [K]; exact_mod_cast hk
      nlinarith only [hK3, sq_nonneg (K - 1)]
    have hscale2 : 0 ≤ 4 * (K ^ 2 - K) * q ^ n :=
      mul_nonneg (by nlinarith only [hKleSq]) (pow_nonneg hq n)
    nlinarith only [hscale, hscale2]

/-- Every digit point is in a ball whose radius is quadratic in the
largest place value. -/
theorem digitPoint_radius (k n : ℕ) (hk : 3 ≤ k)
    (α : Fin n → Fin (k - 1)) :
    dist (digitPoint k n α) 0 ≤
      16 * (k : ℝ) ^ 2 * (((k : ℝ) ^ 2) ^ n) := by
  let K : ℝ := k
  let X : ℝ := (xCoord k n α : ℝ)
  let Y : ℝ := (yCoord k n α : ℝ)
  let q : ℝ := K ^ 2
  have hK : 3 ≤ K := by dsimp [K]; exact_mod_cast hk
  have hK0 : 0 ≤ K := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hX₀ : 0 ≤ X := by
    dsimp [X]
    exact_mod_cast (xCoord_bound k n hk α).1
  have hX₁ : X ≤ K ^ n := by
    dsimp [X, K]
    exact_mod_cast (xCoord_bound k n hk α).2.le
  have hY₀ : 0 ≤ Y := by
    dsimp [Y]
    exact_mod_cast (yCoord_bound k n hk α).1
  have hY₁ : Y ≤ 4 * K ^ 2 * q ^ n := by
    dsimp [Y, K, q]
    exact_mod_cast (yCoord_bound k n hk α).2.le
  have hKq : K ≤ q := by dsimp [q]; nlinarith
  have hX₂ : X ≤ q ^ n := by
    calc
      X ≤ K ^ n := hX₁
      _ ≤ q ^ n := by gcongr
  have hqpow : 0 ≤ q ^ n := pow_nonneg hq n
  have hcoeff : 0 ≤ 15 * K ^ 2 - 1 := by nlinarith
  have hsum : X + Y ≤ 16 * K ^ 2 * q ^ n := by
    nlinarith [mul_nonneg hcoeff hqpow]
  have hdist : dist (digitPoint k n α) 0 = Real.sqrt (X ^ 2 + Y ^ 2) := by
    rw [EuclideanSpace.dist_eq]
    simp only [Fin.sum_univ_two, digitPoint_zero, digitPoint_one,
      Pi.zero_apply, Real.dist_eq]
    rw [sq_abs, sq_abs]
    norm_num [X, Y]
  rw [hdist]
  have hbase : 0 ≤ X ^ 2 + Y ^ 2 := by positivity
  have hs0 : 0 ≤ Real.sqrt (X ^ 2 + Y ^ 2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (X ^ 2 + Y ^ 2) ^ 2 = X ^ 2 + Y ^ 2 :=
    Real.sq_sqrt hbase
  have hsq : Real.sqrt (X ^ 2 + Y ^ 2) ≤ X + Y := by
    nlinarith [mul_nonneg hX₀ hY₀]
  exact hsq.trans hsum

#print axioms digitPoint_radius

#print axioms xCoord_bound
#print axioms yCoord_bound

end Erdos953Lower
