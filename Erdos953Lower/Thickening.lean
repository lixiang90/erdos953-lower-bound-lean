/-
  Erdős Problem 953: turn a finite robust point configuration into
  a measurable set by thickening every point to a small open disk.
-/
import Erdos953Lower.PointGap
import Erdos953Lower.PointSize
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace Erdos953Lower

open MeasureTheory

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The union of congruent open disks centered at a finite set. -/
def thickening (P : Finset Plane) (ρ : ℝ) : Set Plane :=
  ⋃ p ∈ P, Metric.ball p ρ

/-- Enlarging the centers by a sufficiently small radius preserves
avoidance of positive integer distances. -/
theorem thickening_no_positive_integer_distances
    (P : Finset Plane) (δ ρ : ℝ)
    (h2ρδ : 2 * ρ < δ) (h2ρ1 : 2 * ρ < 1)
    (haway : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ∀ z : ℤ, δ < |dist p q - (z : ℝ)|) :
    ∀ x ∈ thickening P ρ, ∀ y ∈ thickening P ρ,
      x ≠ y → ∀ n : ℕ, 0 < n → dist x y ≠ (n : ℝ) := by
  intro x hx y hy hxy n hn hdist
  obtain ⟨p, hp, hxp⟩ : ∃ p ∈ P, x ∈ Metric.ball p ρ := by
    simpa [thickening] using hx
  obtain ⟨q, hq, hyq⟩ : ∃ q ∈ P, y ∈ Metric.ball q ρ := by
    simpa [thickening] using hy
  have hxp' : dist x p < ρ := by simpa [Metric.mem_ball, dist_comm] using hxp
  have hyq' : dist y q < ρ := by simpa [Metric.mem_ball, dist_comm] using hyq
  by_cases hpq : p = q
  · subst q
    have hpy : dist p y < ρ := by simpa only [dist_comm] using hyq'
    have hsmall : dist x y < 2 * ρ := by
      calc
        dist x y ≤ dist x p + dist p y := dist_triangle x p y
        _ < ρ + ρ := by linarith [hxp', hpy]
        _ = 2 * ρ := by ring
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  · have hcenter := haway p hp q hq hpq (n : ℤ)
    have hcenter' : δ < |dist p q - (n : ℝ)| := by simpa using hcenter
    have hclose : |dist p q - (n : ℝ)| ≤ dist x p + dist y q := by
      have h := dist_dist_dist_le x y p q
      rw [hdist] at h
      simpa [Real.dist_eq, abs_sub_comm] using h
    linarith [hcenter', hxp', hyq']

/-- A finite union of open disks is measurable. -/
theorem thickening_measurable (P : Finset Plane) (ρ : ℝ) :
    MeasurableSet (thickening P ρ) := by
  unfold thickening
  exact Finset.measurableSet_biUnion P (fun _ _ => Metric.isOpen_ball.measurableSet)

/-- The disks are disjoint when the center-to-center gap exceeds twice the radius. -/
theorem thickening_pairwiseDisjoint
    (P : Finset Plane) (δ ρ : ℝ) (h2ρδ : 2 * ρ < δ)
    (haway : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ∀ z : ℤ, δ < |dist p q - (z : ℝ)|) :
    Set.PairwiseDisjoint (P : Set Plane) (fun p => Metric.ball p ρ) := by
  intro p hp q hq hpq
  apply Metric.ball_disjoint_ball
  have hsep := haway p hp q hq hpq 0
  have hsep' : δ < dist p q := by simpa [abs_of_nonneg dist_nonneg] using hsep
  linarith

/-- Exact area of the union of congruent disks. -/
theorem thickening_volume
    (P : Finset Plane) (δ ρ : ℝ) (h2ρδ : 2 * ρ < δ)
    (haway : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ∀ z : ℤ, δ < |dist p q - (z : ℝ)|) :
    volume (thickening P ρ) =
      (P.card : ENNReal) * (ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal Real.pi) := by
  rw [thickening, measure_biUnion_finset
    (thickening_pairwiseDisjoint P δ ρ h2ρδ haway)
    (fun _ _ => Metric.isOpen_ball.measurableSet)]
  simp

end Erdos953Lower
