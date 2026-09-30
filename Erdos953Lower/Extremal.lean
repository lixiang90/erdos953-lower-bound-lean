import Erdos953Lower.Polylog

/-!
The open-disk extremal area from Erdős Problem #953, defined independently of
any upper-bound formalization. This keeps the lower-bound statement and its
Lean proof usable on their own.
-/

noncomputable section

namespace Erdos953Lower

open MeasureTheory
open scoped ENNReal

/-- A measurable subset of the open disk with no positive integer distance
between any two distinct points. -/
def AdmissibleOpenSet (R : ℝ) (A : Set Plane) : Prop :=
  MeasurableSet A ∧ A ⊆ Metric.ball (0 : Plane) R ∧
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ))

/-- Lebesgue area, converted from an extended nonnegative real to a real. -/
def area (A : Set Plane) : ℝ := (volume A).toReal

/-- Supremal admissible area for a disk of radius `R`. -/
def Mopen (R : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ A : Set Plane, AdmissibleOpenSet R A ∧ area A = a}

theorem area_le_Mopen_of_admissible {R : ℝ} {A : Set Plane}
    (hA : AdmissibleOpenSet R A) : area A ≤ Mopen R := by
  have hballfin : volume (Metric.closedBall (0 : Plane) R) < ∞ := by
    rw [EuclideanSpace.volume_closedBall]
    finiteness
  have hbounded :
      BddAbove {a : ℝ | ∃ B : Set Plane, AdmissibleOpenSet R B ∧ area B = a} := by
    refine ⟨(volume (Metric.closedBall (0 : Plane) R)).toReal, ?_⟩
    rintro a ⟨B, hB, rfl⟩
    exact ENNReal.toReal_mono (ne_of_lt hballfin)
      (measure_mono (hB.2.1.trans Metric.ball_subset_closedBall))
  have hmem : area A ∈
      {a : ℝ | ∃ B : Set Plane, AdmissibleOpenSet R B ∧ area B = a} :=
    ⟨A, hA, rfl⟩
  exact le_csSup hbounded hmem

/-- The original digit-disk construction gives a lower bound for the
standalone extremal area. -/
theorem lower_bound_for_Mopen :
    ∀ ε : ℝ, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
        ∀ R : ℝ, R₀ ≤ R → c * R ^ (1 / 2 - ε) ≤ Mopen R := by
  intro ε hε
  obtain ⟨c, hc, R₀, hlow⟩ := erdos953_lower ε hε
  refine ⟨c, hc, R₀, ?_⟩
  intro R hR
  obtain ⟨A, hmeas, hball, hno, harea⟩ := hlow R hR
  exact harea.trans (area_le_Mopen_of_admissible ⟨hmeas, hball, hno⟩)

/-- Explicit near-square-root lower bound for the standalone extremal area. -/
theorem lower_polylog_for_Mopen (R : ℝ)
    (hR : (1000 : ℝ) ^ 4 ≤ R) :
    ((1 : ℝ) / (100000 * (Real.log R + 3) ^ 10)) *
      (Real.exp (-1) * Real.sqrt R) ≤ Mopen R := by
  obtain ⟨A, hmeas, hball, hno, harea⟩ := erdos953_lower_polylog R hR
  exact harea.trans (area_le_Mopen_of_admissible ⟨hmeas, hball, hno⟩)

#print axioms area_le_Mopen_of_admissible
#print axioms lower_bound_for_Mopen
#print axioms lower_polylog_for_Mopen

end Erdos953Lower
