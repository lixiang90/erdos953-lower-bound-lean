import Erdos953Formalization.MeasureReduction

/-!
The original Erdős 953 question uses an open disk. Hart's extremal-area
definition uses a closed disk. Their attainable area sets are identical:
removing the null boundary sphere preserves area and admissibility.
-/

noncomputable section

namespace Erdos953OpenClosed

open Erdos953Formalization
open MeasureTheory

/-- Admissibility for the open disk used in the original problem wording. -/
def AdmissibleOpenSet (R : ℝ) (A : Set Plane) : Prop :=
  MeasurableSet A ∧ A ⊆ Metric.ball (0 : Plane) R ∧
    NoPositiveIntegerDistances A

/-- Extremal area when the containing disk is open. -/
def Mopen (R : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ A : Set Plane, AdmissibleOpenSet R A ∧ area A = a}

private lemma volume_sphere_zero (R : ℝ) :
    volume (Metric.sphere (0 : Plane) R) = 0 := by
  exact Measure.addHaar_sphere (volume : Measure Plane) 0 R

private lemma closed_admissible_to_open {R : ℝ} {A : Set Plane}
    (hA : AdmissibleSet R A) :
    AdmissibleOpenSet R (A \ Metric.sphere (0 : Plane) R) ∧
      area (A \ Metric.sphere (0 : Plane) R) = area A := by
  have hsub : A \ Metric.sphere (0 : Plane) R ⊆
      Metric.ball (0 : Plane) R := by
    intro x hx
    have hclosed : dist x 0 ≤ R := Metric.mem_closedBall.mp
      (hA.subset_closedBall hx.1)
    have hne : dist x 0 ≠ R := by
      intro heq
      exact hx.2 (Metric.mem_sphere.mpr heq)
    exact Metric.mem_ball.mpr (lt_of_le_of_ne hclosed hne)
  have hdist : NoPositiveIntegerDistances
      (A \ Metric.sphere (0 : Plane) R) :=
    hA.noPositiveIntegerDistances.mono Set.sdiff_subset
  have hmeas : MeasurableSet (A \ Metric.sphere (0 : Plane) R) :=
    hA.1.diff Metric.isClosed_sphere.measurableSet
  refine ⟨⟨hmeas, hsub, hdist⟩, ?_⟩
  unfold area
  rw [measure_sdiff_null (volume_sphere_zero R)]

/-- The open- and closed-disk formulations have the same attainable areas. -/
theorem attainable_areas_eq (R : ℝ) :
    {a : ℝ | ∃ A : Set Plane, AdmissibleOpenSet R A ∧ area A = a} =
      {a : ℝ | ∃ A : Set Plane, AdmissibleSet R A ∧ area A = a} := by
  ext a
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A, ⟨hA.1, hA.2.1.trans Metric.ball_subset_closedBall,
      hA.2.2⟩, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨hopen, harea⟩ := closed_admissible_to_open hA
    exact ⟨A \ Metric.sphere (0 : Plane) R, hopen, harea⟩

/-- Open- and closed-disk extremal area agree at every radius. -/
theorem Mopen_eq_M (R : ℝ) : Mopen R = M R := by
  unfold Mopen M
  rw [attainable_areas_eq R]

end Erdos953OpenClosed

#print axioms Erdos953OpenClosed.Mopen_eq_M
