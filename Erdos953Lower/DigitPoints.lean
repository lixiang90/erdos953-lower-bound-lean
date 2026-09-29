/-
  Erdős Problem 953: finite planar point sets from base-k digits.
  The construction follows the two-dimensional Sárközy scheme.
-/
import Erdos953Lower.Digits
import Erdos953Lower.FiniteGap
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

namespace Erdos953Lower

open Finset

/-- Horizontal coordinate of a finite digit string. -/
def xCoord (k n : ℕ) (α : Fin n → Fin (k - 1)) : ℤ :=
  ∑ j ∈ range n, digitAt k n α j * (k : ℤ) ^ j

/-- Vertical coordinate, with squared-place weights. -/
def yCoord (k n : ℕ) (α : Fin n → Fin (k - 1)) : ℤ :=
  8 * (k : ℤ) ^ 2 *
    ∑ j ∈ range n, digitAt k n α j * (((k : ℤ) ^ 2) ^ j)

/-- A point in the Euclidean plane associated to a digit string. -/
def digitPoint (k n : ℕ) (α : Fin n → Fin (k - 1)) :
    EuclideanSpace ℝ (Fin 2) :=
  !₂[((xCoord k n α : ℤ) : ℝ), ((yCoord k n α : ℤ) : ℝ)]

@[simp] lemma digitPoint_zero (k n : ℕ) (α : Fin n → Fin (k - 1)) :
    digitPoint k n α 0 = (xCoord k n α : ℝ) := by
  simp [digitPoint]

@[simp] lemma digitPoint_one (k n : ℕ) (α : Fin n → Fin (k - 1)) :
    digitPoint k n α 1 = (yCoord k n α : ℝ) := by
  simp [digitPoint]

/-- Terms above the highest differing position vanish, so the full digit
sum equals its initial segment. -/
lemma digitDiff_sum_truncate (k n i : ℕ)
    (α β : Fin n → Fin (k - 1)) (hi : i < n)
    (hzero : ∀ j, i < j → digitDiff k n α β j = 0)
    (q : ℤ) :
    (∑ j ∈ range n, digitDiff k n α β j * q ^ j) =
      ∑ j ∈ range (i + 1), digitDiff k n α β j * q ^ j := by
  apply (sum_subset (by simp [hi] : range (i + 1) ⊆ range n) ?_).symm
  intro j hj hjnot
  have hij : i < j := by
    have : ¬ j < i + 1 := by simpa using hjnot
    omega
  simp [hzero j hij]

lemma xCoord_sub (k n : ℕ) (α β : Fin n → Fin (k - 1)) :
    xCoord k n α - xCoord k n β =
      ∑ j ∈ range n, digitDiff k n α β j * (k : ℤ) ^ j := by
  rw [xCoord, xCoord, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  simp [digitDiff, sub_mul]

lemma yCoord_sub (k n : ℕ) (α β : Fin n → Fin (k - 1)) :
    yCoord k n α - yCoord k n β =
      8 * (k : ℤ) ^ 2 *
      ∑ j ∈ range n, digitDiff k n α β j * (((k : ℤ) ^ 2) ^ j) := by
  rw [yCoord, yCoord, ← mul_sub]
  congr 1
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  simp [digitDiff, sub_mul]

/-- Exact Euclidean distance of two digit points, expressed through their
integral coordinate differences. -/
lemma digitPoint_dist (k n : ℕ) (α β : Fin n → Fin (k - 1)) :
    dist (digitPoint k n α) (digitPoint k n β) =
      Real.sqrt (((xCoord k n α - xCoord k n β : ℤ) : ℝ) ^ 2 +
        ((yCoord k n α - yCoord k n β : ℤ) : ℝ) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, digitPoint_zero, digitPoint_one, Real.dist_eq]
  rw [sq_abs, sq_abs]
  norm_num

end Erdos953Lower
