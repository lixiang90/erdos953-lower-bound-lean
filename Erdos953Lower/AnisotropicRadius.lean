/- Sharper radius estimates for the existing base-k digit centers. -/
import Erdos953Lower.PointSize

namespace Erdos953Lower

open Finset

set_option maxHeartbeats 50000

/-- The geometric series cancels the extra base factor in the old bound. -/
theorem yCoord_bound_sharp (k n : ℕ) (hk : 3 ≤ k)
    (α : Fin n → Fin (k - 1)) :
    0 ≤ yCoord k n α ∧
      yCoord k n α < 8 * (((k : ℤ) ^ 2) ^ n) := by
  let K : ℤ := k
  let q : ℤ := K ^ 2
  let T : ℤ := ∑ j ∈ range n, digitAt k n α j * q ^ j
  let S : ℤ := ∑ j ∈ range n, q ^ j
  have hK : 3 ≤ K := by dsimp [K]; exact_mod_cast hk
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hTlo : 0 ≤ T := by
    dsimp [T]
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (digitAt_nonneg k n α j) (pow_nonneg hq j)
  have hSlo : 0 ≤ S := by
    dsimp [S]
    apply sum_nonneg
    intro j hj
    exact pow_nonneg hq j
  have hThi : T ≤ (K - 2) * S := by
    dsimp [T, S]
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right
      (digitAt_le k n hk α j) (pow_nonneg hq j)
  have hid := geom_sum_mul_add (q - 1) n
  have hbase : q - 1 + 1 = q := by ring
  rw [hbase] at hid
  have hcoef : K * (K - 2) ≤ q - 1 := by
    dsimp [q]
    nlinarith only [hK]
  have hKT : K * T < q ^ n := by
    have h₁ := mul_le_mul_of_nonneg_left hThi hK0
    have h₂ := mul_le_mul_of_nonneg_right hcoef hSlo
    change S * (q - 1) + 1 = q ^ n at hid
    nlinarith only [h₁, h₂, hid]
  constructor
  · change 0 ≤ 8 * K * T
    positivity
  · change 8 * K * T < 8 * q ^ n
    linarith only [hKT]

/-- All centers lie within `9 k^(2n)`, independently of an additional
power of the base. -/
theorem digitPoint_radius_sharp (k n : ℕ) (hk : 3 ≤ k)
    (α : Fin n → Fin (k - 1)) :
    dist (digitPoint k n α) 0 < 9 * (((k : ℝ) ^ 2) ^ n) := by
  let K : ℝ := k
  let X : ℝ := (xCoord k n α : ℝ)
  let Y : ℝ := (yCoord k n α : ℝ)
  let q : ℝ := K ^ 2
  have hK : 3 ≤ K := by dsimp [K]; exact_mod_cast hk
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact_mod_cast (xCoord_bound k n hk α).1
  have hX1 : X < K ^ n := by
    dsimp [X, K]
    exact_mod_cast (xCoord_bound k n hk α).2
  have hY0 : 0 ≤ Y := by
    dsimp [Y]
    exact_mod_cast (yCoord_bound_sharp k n hk α).1
  have hY1 : Y < 8 * q ^ n := by
    dsimp [Y, K, q]
    exact_mod_cast (yCoord_bound_sharp k n hk α).2
  have hKq : K ≤ q := by dsimp [q]; nlinarith only [hK]
  have hX2 : X < q ^ n := hX1.trans_le (by gcongr)
  have hsum : X + Y < 9 * q ^ n := by linarith only [hX2, hY1]
  have hdist : dist (digitPoint k n α) 0 = Real.sqrt (X ^ 2 + Y ^ 2) := by
    rw [EuclideanSpace.dist_eq]
    simp only [Fin.sum_univ_two, digitPoint_zero, digitPoint_one,
      Real.dist_eq]
    rw [sq_abs, sq_abs]
    norm_num [X, Y]
  rw [hdist]
  have hbase : 0 ≤ X ^ 2 + Y ^ 2 := by positivity
  have hs0 := Real.sqrt_nonneg (X ^ 2 + Y ^ 2)
  have hs2 := Real.sq_sqrt hbase
  have hsum0 : 0 ≤ X + Y := by linarith only [hX0, hY0]
  have hsq : Real.sqrt (X ^ 2 + Y ^ 2) ≤ X + Y := by
    nlinarith only [hs0, hs2, hsum0, mul_nonneg hX0 hY0]
  exact hsq.trans_lt hsum

#print axioms yCoord_bound_sharp
#print axioms digitPoint_radius_sharp

end Erdos953Lower
