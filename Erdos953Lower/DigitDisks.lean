/-
  The finite digit configuration, thickened to a positive-area measurable set.
-/
import Erdos953Lower.Thickening

namespace Erdos953Lower

open MeasureTheory

noncomputable section

def gap (k : ℕ) : ℝ := 1 / (48 * (k : ℝ) ^ 5)
def diskRadius (k : ℕ) : ℝ := gap k / 4

private theorem gap_pos (k : ℕ) (hk : 3 ≤ k) : 0 < gap k := by
  unfold gap
  positivity

private theorem gap_lt_one (k : ℕ) (hk : 3 ≤ k) : gap k < 1 := by
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hpow : (1 : ℝ) ≤ (k : ℝ) ^ 5 := one_le_pow₀ hK
  have hden : 0 < 48 * (k : ℝ) ^ 5 := by positivity
  unfold gap
  rw [div_lt_iff₀ hden]
  nlinarith

private theorem twice_diskRadius_lt_gap (k : ℕ) (hk : 3 ≤ k) :
    2 * diskRadius k < gap k := by
  unfold diskRadius
  linarith [gap_pos k hk]

private theorem twice_diskRadius_lt_one (k : ℕ) (hk : 3 ≤ k) :
    2 * diskRadius k < 1 := by
  linarith [twice_diskRadius_lt_gap k hk, gap_lt_one k hk]

theorem diskRadius_lt_one (k : ℕ) (hk : 3 ≤ k) : diskRadius k < 1 := by
  unfold diskRadius
  linarith [gap_pos k hk, gap_lt_one k hk]

/-- The union of one open disk per digit point. -/
def digitDisks (k n : ℕ) : Set Plane :=
  thickening (digitPointSet k n) (diskRadius k)

theorem digitDisks_measurable (k n : ℕ) : MeasurableSet (digitDisks k n) :=
  thickening_measurable _ _

theorem digitDisks_no_positive_integer_distances
    (k n : ℕ) (hk : 3 ≤ k) :
    ∀ x ∈ digitDisks k n, ∀ y ∈ digitDisks k n,
      x ≠ y → ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ) := by
  exact thickening_no_positive_integer_distances
    (digitPointSet k n) (gap k) (diskRadius k)
    (twice_diskRadius_lt_gap k hk) (twice_diskRadius_lt_one k hk)
    (fun p hp q hq hpq z => digitPointSet_away k n hk hp hq hpq z)

theorem digitDisks_volume (k n : ℕ) (hk : 3 ≤ k) :
    volume (digitDisks k n) =
      (((k - 1) ^ n : ℕ) : ENNReal) *
        (ENNReal.ofReal (diskRadius k) ^ 2 * ENNReal.ofReal Real.pi) := by
  unfold digitDisks
  rw [thickening_volume (digitPointSet k n) (gap k) (diskRadius k)
    (twice_diskRadius_lt_gap k hk)
    (fun p hp q hq hpq z => digitPointSet_away k n hk hp hq hpq z)]
  rw [digitPointSet_card k n hk]

theorem digitDisks_subset_ball (k n : ℕ) (hk : 3 ≤ k) :
    digitDisks k n ⊆ Metric.ball (0 : Plane)
      (16 * (k : ℝ) ^ 2 * (((k : ℝ) ^ 2) ^ n) + diskRadius k) := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ : ∃ p ∈ digitPointSet k n,
      x ∈ Metric.ball p (diskRadius k) := by
    simpa [digitDisks, thickening] using hx
  obtain ⟨α, _, rfl⟩ := Finset.mem_image.mp hp
  have hxp' : dist x (digitPoint k n α) < diskRadius k := by
    simpa [Metric.mem_ball, dist_comm] using hxp
  have hp0 := digitPoint_radius k n hk α
  have hx0 : dist x (0 : Plane) <
      16 * (k : ℝ) ^ 2 * (((k : ℝ) ^ 2) ^ n) + diskRadius k := by
    calc
      dist x 0 ≤ dist x (digitPoint k n α) + dist (digitPoint k n α) 0 :=
        dist_triangle x (digitPoint k n α) 0
      _ < 16 * (k : ℝ) ^ 2 * (((k : ℝ) ^ 2) ^ n) + diskRadius k := by
        linarith
  simpa [Metric.mem_ball, dist_comm] using hx0

/-- A single theorem packaging the finite lower-bound construction in an open ball. -/
theorem digitDisks_finite_lower_witness (k n : ℕ) (hk : 3 ≤ k) :
    ∃ A : Set Plane,
      MeasurableSet A ∧
      A ⊆ Metric.ball (0 : Plane)
        (16 * (k : ℝ) ^ 2 * (((k : ℝ) ^ 2) ^ n) + diskRadius k) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ)) ∧
      volume A = (((k - 1) ^ n : ℕ) : ENNReal) *
        (ENNReal.ofReal (diskRadius k) ^ 2 * ENNReal.ofReal Real.pi) := by
  refine ⟨digitDisks k n, digitDisks_measurable k n, ?_,
    digitDisks_no_positive_integer_distances k n hk, digitDisks_volume k n hk⟩
  exact digitDisks_subset_ball k n hk

#print axioms digitDisks_no_positive_integer_distances
#print axioms digitDisks_volume
#print axioms digitDisks_subset_ball
#print axioms digitDisks_finite_lower_witness

end

end Erdos953Lower
