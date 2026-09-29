/-
  Erdős Problem 953: locate the highest differing digit in two finite
  base-k strings and bound all preceding digit differences.
-/
import Erdos953Lower.DigitControl
import Mathlib.Data.Finset.Max

namespace Erdos953Lower

open Finset

/-- The digit at position `j`, extended by zero beyond the string length. -/
def digitAt (k n : ℕ) (α : Fin n → Fin (k - 1)) (j : ℕ) : ℤ :=
  if h : j < n then ((α ⟨j, h⟩).val : ℤ) else 0

/-- Signed digit difference between two strings. -/
def digitDiff (k n : ℕ)
    (α β : Fin n → Fin (k - 1)) (j : ℕ) : ℤ :=
  digitAt k n α j - digitAt k n β j

lemma digitDiff_eq_zero_of_ge (k n : ℕ)
    (α β : Fin n → Fin (k - 1)) {j : ℕ} (hj : n ≤ j) :
    digitDiff k n α β j = 0 := by
  simp [digitDiff, digitAt, not_lt.mpr hj]

lemma digitDiff_abs_le (k n : ℕ) (hk : 3 ≤ k)
    (α β : Fin n → Fin (k - 1)) {j : ℕ} (hj : j < n) :
    |digitDiff k n α β j| ≤ (k : ℤ) - 2 := by
  have hu : (α ⟨j, hj⟩).val ≤ k - 2 := by
    have h := (α ⟨j, hj⟩).isLt
    omega
  have hv : (β ⟨j, hj⟩).val ≤ k - 2 := by
    have h := (β ⟨j, hj⟩).isLt
    omega
  simpa [digitDiff, digitAt, hj] using
    digit_difference_abs_le k (α ⟨j, hj⟩).val (β ⟨j, hj⟩).val (by omega) hu hv

/-- The maximal differing index gives the hypotheses of the leading-digit
distance theorem. -/
theorem exists_highest_digit_difference (k n : ℕ) (hk : 3 ≤ k)
    (α β : Fin n → Fin (k - 1)) (hab : α ≠ β) :
    ∃ i < n,
      digitDiff k n α β i ≠ 0 ∧
      (∀ j, i < j → digitDiff k n α β j = 0) ∧
      (∀ j ≤ i, |digitDiff k n α β j| ≤ (k : ℤ) - 2) := by
  have hex : ∃ z : Fin n, α z ≠ β z := by
    by_contra h
    push_neg at h
    apply hab
    funext z
    exact h z
  let S : Finset ℕ := (range n).filter (fun j => digitDiff k n α β j ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨z, hz⟩ := hex
    refine ⟨z.val, ?_⟩
    have hzdiff : digitDiff k n α β z.val ≠ 0 := by
      simp only [digitDiff, digitAt, z.isLt, dite_true]
      intro heq
      have hval : (α z).val = (β z).val := by exact_mod_cast (sub_eq_zero.mp heq)
      exact hz (Fin.ext hval)
    simp [S, z.isLt, hzdiff]
  let i := S.max' hS
  have himem : i ∈ S := S.max'_mem hS
  have hirange : i < n := (mem_range.mp ((mem_filter.mp himem).1))
  have hidiff : digitDiff k n α β i ≠ 0 := (mem_filter.mp himem).2
  refine ⟨i, hirange, hidiff, ?_, ?_⟩
  · intro j hij
    by_cases hj : j < n
    · by_contra hne
      have hjmem : j ∈ S := mem_filter.mpr ⟨mem_range.mpr hj, hne⟩
      exact (not_le_of_gt hij) (S.le_max' j hjmem)
    · exact digitDiff_eq_zero_of_ge k n α β (not_lt.mp hj)
  · intro j hji
    exact digitDiff_abs_le k n hk α β (lt_of_le_of_lt hji hirange)

#print axioms exists_highest_digit_difference

end Erdos953Lower
