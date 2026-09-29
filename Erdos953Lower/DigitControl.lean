/-
  Erdős Problem 953: absolute-value control for finite digit sums.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace Erdos953Lower

open Finset

/-- Uniform bounds on signed digits imply the corresponding geometric
upper bound for any partial sum. -/
theorem weighted_digit_sum_abs_le (q C : ℤ) (i : ℕ) (d : ℕ → ℤ)
    (hq : 0 ≤ q) (hd : ∀ j < i, |d j| ≤ C) :
    |∑ j ∈ range i, d j * q ^ j| ≤
      C * ∑ j ∈ range i, q ^ j := by
  calc
    |∑ j ∈ range i, d j * q ^ j|
        ≤ ∑ j ∈ range i, |d j * q ^ j| :=
          abs_sum_le_sum_abs (fun j ↦ d j * q ^ j) (range i)
    _ = ∑ j ∈ range i, |d j| * q ^ j := by
          apply sum_congr rfl
          intro j hj
          rw [abs_mul, abs_of_nonneg (pow_nonneg hq j)]
    _ ≤ ∑ j ∈ range i, C * q ^ j := by
          apply sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_right (hd j (mem_range.mp hj))
            (pow_nonneg hq j)
    _ = C * ∑ j ∈ range i, q ^ j := by rw [mul_sum]

/-- The difference of two digits in `{0, ..., k-2}` has magnitude at most
`k-2`. This will instantiate `weighted_digit_sum_abs_le`. -/
theorem digit_difference_abs_le (k u v : ℕ)
    (hk : 2 ≤ k) (hu : u ≤ k - 2) (hv : v ≤ k - 2) :
    |(u : ℤ) - (v : ℤ)| ≤ (k : ℤ) - 2 := by
  have hu' : (u : ℤ) ≤ (k : ℤ) - 2 := by exact_mod_cast hu
  have hv' : (v : ℤ) ≤ (k : ℤ) - 2 := by exact_mod_cast hv
  rw [abs_le]
  constructor <;> omega

#print axioms weighted_digit_sum_abs_le
#print axioms digit_difference_abs_le

end Erdos953Lower
