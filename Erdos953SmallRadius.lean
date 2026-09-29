import Erdos953Formalization.MeasureReduction

/-!
Exact extremal area for radius at most one half. This is a local result toward
the full Erdős 953 extremal-area question; it does not determine `M R` at
arbitrary radius.
-/

noncomputable section

namespace Erdos953SmallRadius

open Erdos953Formalization
open MeasureTheory

private def definingSet (R : ℝ) : Set ℝ :=
  {a : ℝ | ∃ A : Set Plane, AdmissibleSet R A ∧ area A = a}

private lemma definingSet_bddAbove (R : ℝ) : BddAbove (definingSet R) := by
  refine ⟨area (Metric.closedBall (0 : Plane) R), ?_⟩
  rintro a ⟨A, hA, rfl⟩
  exact area_mono_of_subset_of_finite hA.subset_closedBall
    (volume_closedBall_plane_lt_top 0 R)

private lemma area_ball_eq_area_closedBall (R : ℝ) :
    area (Metric.ball (0 : Plane) R) =
      area (Metric.closedBall (0 : Plane) R) := by
  simp [area]

private lemma small_ball_avoids_integer_distances (R : ℝ)
    (hR : R ≤ 1 / 2) :
    NoPositiveIntegerDistances (Metric.ball (0 : Plane) R) := by
  intro x hx y hy hxy m hm hdist
  have hxR : dist x 0 < R := by
    simpa [Metric.mem_ball] using hx
  have hyR : dist 0 y < R := by
    simpa [Metric.mem_ball, dist_comm] using hy
  have hxy1 : dist x y < 1 := by
    calc
      dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
      _ < 1 := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

/-- Every admissible set has area at most that of its containing disk. -/
theorem M_le_disk_area (R : ℝ) :
    M R ≤ area (Metric.closedBall (0 : Plane) R) := by
  apply M_le_of_admissible_area_bound
  intro A hA
  exact area_mono_of_subset_of_finite hA.subset_closedBall
    (volume_closedBall_plane_lt_top 0 R)

/-- For radius at most one half, the open disk itself avoids positive integer
distances and has the full disk area. -/
theorem M_eq_disk_area_of_le_half (R : ℝ) (hR : R ≤ 1 / 2) :
    M R = area (Metric.closedBall (0 : Plane) R) := by
  apply le_antisymm (M_le_disk_area R)
  have hA : AdmissibleSet R (Metric.ball (0 : Plane) R) := by
    exact ⟨measurableSet_ball, Metric.ball_subset_closedBall,
      small_ball_avoids_integer_distances R hR⟩
  rw [← area_ball_eq_area_closedBall R]
  change area (Metric.ball (0 : Plane) R) ≤ sSup (definingSet R)
  exact le_csSup (definingSet_bddAbove R) ⟨Metric.ball (0 : Plane) R, hA, rfl⟩

/-- The exact small-radius value is the ordinary disk area, including the
boundary case `R = 1/2`. -/
theorem M_eq_pi_mul_sq_of_le_half (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1 / 2) :
    M R = Real.pi * R ^ 2 := by
  rw [M_eq_disk_area_of_le_half R hR,
    area_closedBall_plane_eq_pi_mul_sq 0 hR0]

end Erdos953SmallRadius

#print axioms Erdos953SmallRadius.M_eq_pi_mul_sq_of_le_half
