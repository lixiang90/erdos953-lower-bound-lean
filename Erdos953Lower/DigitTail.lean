/-
  Erdős Problem 953: geometric tails for the finite digit construction.
  A digit at place i dominates all lower places when the digits range
  from 0 through k - 2. The squared-place version has a factor-two margin.
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

namespace Erdos953Lower

open Finset

/-- The total possible contribution from lower base-k digits is strictly
smaller than one unit in place i. -/
theorem linear_digit_tail (k i : ℕ) (hk : 3 ≤ k) :
    ((k : ℤ) - 2) * (∑ j ∈ range i, (k : ℤ) ^ j) < (k : ℤ) ^ i := by
  have hK : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hsum : 0 ≤ ∑ j ∈ range i, (k : ℤ) ^ j := by
    apply sum_nonneg
    intro j hj
    positivity
  have hid := geom_sum_mul_add ((k : ℤ) - 1) i
  have hbase : ((k : ℤ) - 1) + 1 = (k : ℤ) := by ring
  rw [hbase] at hid
  nlinarith

/-- With base-k squared-place weights, the lower digits consume less than
half of the leading place. -/
theorem quadratic_digit_tail (k i : ℕ) (hk : 3 ≤ k) :
    2 * ((k : ℤ) - 2) * (∑ j ∈ range i, ((k : ℤ) ^ 2) ^ j) <
      ((k : ℤ) ^ 2) ^ i := by
  have hK : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hsum : 0 ≤ ∑ j ∈ range i, ((k : ℤ) ^ 2) ^ j := by
    apply sum_nonneg
    intro j hj
    positivity
  have hid := geom_sum_mul_add (((k : ℤ) ^ 2) - 1) i
  have hbase : (((k : ℤ) ^ 2) - 1) + 1 = (k : ℤ) ^ 2 := by ring
  rw [hbase] at hid
  have hcoef : 2 * ((k : ℤ) - 2) ≤ ((k : ℤ) ^ 2) - 1 := by
    nlinarith
  have hmul := mul_nonneg (sub_nonneg.mpr hcoef) hsum
  nlinarith

#print axioms linear_digit_tail
#print axioms quadratic_digit_tail

end Erdos953Lower
