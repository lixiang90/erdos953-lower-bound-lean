/-
  Erdős Problem 953: every two different digit strings give points
  whose Euclidean distance avoids all integers by a fixed margin.
-/
import Erdos953Lower.DigitPoints

namespace Erdos953Lower

open Finset

noncomputable section

/-- The main finite configuration property. -/
theorem digitPoint_pair_away (k n : ℕ) (hk : 3 ≤ k)
    (α β : Fin n → Fin (k - 1)) (hab : α ≠ β) :
    1 / (48 * (k : ℝ) ^ 3) <
      distToInt (dist (digitPoint k n α) (digitPoint k n β)) := by
  obtain ⟨i, hi, hdi, hzero, hbound⟩ :=
    exists_highest_digit_difference k n hk α β hab
  let d : ℕ → ℤ := digitDiff k n α β
  let L : ℤ := ∑ j ∈ range (i + 1), d j * (k : ℤ) ^ j
  let Q : ℤ := ∑ j ∈ range (i + 1), d j * (((k : ℤ) ^ 2) ^ j)
  have hx : xCoord k n α - xCoord k n β = L := by
    rw [xCoord_sub]
    exact digitDiff_sum_truncate k n i α β hi hzero (k : ℤ)
  have hy : yCoord k n α - yCoord k n β =
      8 * (k : ℤ) * Q := by
    rw [yCoord_sub]
    rw [digitDiff_sum_truncate k n i α β hi hzero]
  have hgap := finite_digit_distance_gap k i d hk hbound hdi
  have hsq :
      ((L : ℝ) ^ 2 + ((8 * (k : ℤ) * Q : ℤ) : ℝ) ^ 2) =
        (((8 * (k : ℤ) * |Q| : ℤ) : ℝ) ^ 2 +
          ((|L| : ℤ) : ℝ) ^ 2) := by
    push_cast
    simp only [mul_pow, sq_abs]
    ring
  rw [digitPoint_dist, hx, hy, hsq]
  exact hgap

/-- Different digit strings yield different points. -/
theorem digitPoint_injective (k n : ℕ) (hk : 3 ≤ k) :
    Function.Injective (digitPoint k n) := by
  intro α β heq
  by_contra hab
  have hgap := digitPoint_pair_away k n hk α β hab
  rw [heq, dist_self] at hgap
  simp [distToInt] at hgap
  have hnonneg : (0 : ℝ) ≤ ((k : ℝ) ^ 3)⁻¹ * (48 : ℝ)⁻¹ := by positivity
  exact (not_lt_of_ge hnonneg) hgap

/-- The finite point set indexed by all length-n strings. -/
def digitPointSet (k n : ℕ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  Finset.univ.image (digitPoint k n)

theorem digitPointSet_card (k n : ℕ) (hk : 3 ≤ k) :
    (digitPointSet k n).card = (k - 1) ^ n := by
  rw [digitPointSet, Finset.card_image_of_injective _ (digitPoint_injective k n hk)]
  simp

/-- The set has a positive gap from every integer distance. -/
theorem digitPointSet_away (k n : ℕ) (hk : 3 ≤ k)
    {p q : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ digitPointSet k n) (hq : q ∈ digitPointSet k n)
    (hpq : p ≠ q) (z : ℤ) :
    1 / (48 * (k : ℝ) ^ 3) < |dist p q - (z : ℝ)| := by
  obtain ⟨α, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨β, _, rfl⟩ := Finset.mem_image.mp hq
  have hab : α ≠ β := by
    intro h
    exact hpq (congrArg (digitPoint k n) h)
  have hgap := digitPoint_pair_away k n hk α β hab
  have hround : distToInt (dist (digitPoint k n α) (digitPoint k n β)) ≤
      |dist (digitPoint k n α) (digitPoint k n β) - (z : ℝ)| := by
    exact round_le _ z
  exact lt_of_lt_of_le hgap hround

#print axioms digitPoint_pair_away
#print axioms digitPointSet_away

end

end Erdos953Lower
