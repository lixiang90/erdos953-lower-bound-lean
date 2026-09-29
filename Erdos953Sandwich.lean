import Erdos953Lower.Asymptotic
import Erdos953Lower.Polylog
import Erdos953Formalization.Main
import Erdos953OpenClosed
import Erdos953SmallRadius
import Erdos953Defect

/-!
Connects the independently formalized lower construction to the extremal-area
quantity used in Hart's upper-bound formalization. Hart's source is included
here only as an attributed reference for local checking; this bridge does not
claim authorship of his upper-bound proof.
-/

noncomputable section

namespace Erdos953Sandwich

open Erdos953Formalization
open MeasureTheory

/-- Every admissible area's value lies below the extremal supremum. -/
theorem area_le_M_of_admissible {R : ℝ} {A : Set Plane}
    (hA : AdmissibleSet R A) : area A ≤ M R := by
  have hbounded :
      BddAbove {a : ℝ | ∃ B : Set Plane, AdmissibleSet R B ∧ area B = a} := by
    refine ⟨area (Metric.closedBall (0 : Plane) R), ?_⟩
    rintro a ⟨B, hB, rfl⟩
    exact area_mono_of_subset_of_finite hB.subset_closedBall
      (volume_closedBall_plane_lt_top 0 R)
  have hmem : area A ∈
      {a : ℝ | ∃ B : Set Plane, AdmissibleSet R B ∧ area B = a} :=
    ⟨A, hA, rfl⟩
  exact le_csSup hbounded hmem

/-- The lower construction gives an asymptotic lower bound for Hart's `M`. -/
theorem lower_bound_for_M :
    ∀ ε : ℝ, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
        ∀ R : ℝ, R₀ ≤ R → c * R ^ (1 / 2 - ε) ≤ M R := by
  intro ε hε
  obtain ⟨c, hc, R₀, hR₀⟩ := Erdos953Lower.erdos953_lower ε hε
  refine ⟨c, hc, R₀, ?_⟩
  intro R hR
  obtain ⟨A, hmeas, hball, hno, harea⟩ := hR₀ R hR
  have hA : AdmissibleSet R A := by
    refine ⟨hmeas, hball.trans Metric.ball_subset_closedBall, ?_⟩
    exact hno
  exact harea.trans (area_le_M_of_admissible hA)

/-- The explicit polylogarithmic lower bound for the original open-disk
extremal quantity. -/
theorem lower_polylog_for_Mopen (R : ℝ)
    (hR : (1000 : ℝ) ^ 4 ≤ R) :
    ((1 : ℝ) / (100000 * (Real.log R + 3) ^ 12)) *
      (Real.exp (-1) * Real.sqrt R) ≤
        Erdos953OpenClosed.Mopen R := by
  obtain ⟨A, hmeas, hball, hno, harea⟩ :=
    Erdos953Lower.erdos953_lower_polylog R hR
  have hA : AdmissibleSet R A :=
    ⟨hmeas, hball.trans Metric.ball_subset_closedBall, hno⟩
  change _ ≤ area A at harea
  simpa only [Erdos953OpenClosed.Mopen_eq_M] using
    harea.trans (area_le_M_of_admissible hA)

/-- The current explicit lower bound and the attributed upper bound enclose
the open-disk extremal area up to a twelfth power of a logarithm. -/
theorem polylog_sandwich_open :
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℝ, (1000 : ℝ) ^ 4 ≤ R →
        ((1 : ℝ) / (100000 * (Real.log R + 3) ^ 12)) *
          (Real.exp (-1) * Real.sqrt R) ≤
            Erdos953OpenClosed.Mopen R ∧
        Erdos953OpenClosed.Mopen R ≤ C * Real.sqrt R := by
  obtain ⟨C, hC, hupper⟩ := erdos953_upper
  refine ⟨C, hC, ?_⟩
  intro R hR
  constructor
  · exact lower_polylog_for_Mopen R hR
  · simpa only [Erdos953OpenClosed.Mopen_eq_M] using
      hupper R (by nlinarith)

/-- A formal growth-exponent sandwich, without a claim that this fully answers
the original prize question or that the attributed upper proof is ours. -/
theorem growth_sandwich :
    (∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
        ∀ R : ℝ, R₀ ≤ R → c * R ^ (1 / 2 - ε) ≤ M R) :=
  ⟨erdos953_upper, lower_bound_for_M⟩

/-- The same bounds for the original open-disk formulation, using the
zero-area boundary equivalence. -/
theorem growth_sandwich_open :
    (∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      Erdos953OpenClosed.Mopen R ≤ C * Real.sqrt R) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
        ∀ R : ℝ, R₀ ≤ R →
          c * R ^ (1 / 2 - ε) ≤ Erdos953OpenClosed.Mopen R) := by
  obtain ⟨⟨C, hC, hupper⟩, hlower⟩ := growth_sandwich
  refine ⟨⟨C, hC, ?_⟩, ?_⟩
  · intro R hR
    simpa only [Erdos953OpenClosed.Mopen_eq_M] using hupper R hR
  · intro ε hε
    obtain ⟨c, hc, R₀, hlow⟩ := hlower ε hε
    exact ⟨c, hc, R₀, fun R hR => by
      simpa only [Erdos953OpenClosed.Mopen_eq_M] using hlow R hR⟩

/-- Exact small-radius value for the original open-disk definition. -/
theorem Mopen_eq_pi_mul_sq_of_le_half (R : ℝ) (hR0 : 0 ≤ R)
    (hR : R ≤ 1 / 2) :
    Erdos953OpenClosed.Mopen R = Real.pi * R ^ 2 := by
  rw [Erdos953OpenClosed.Mopen_eq_M]
  exact Erdos953SmallRadius.M_eq_pi_mul_sq_of_le_half R hR0 hR

/-- A quantitative area defect for the original open-disk formulation whenever
the radius exceeds one half. -/
theorem explicit_area_defect_open {R : ℝ} (hR : 1 / 2 < R) :
    Erdos953OpenClosed.Mopen R +
      Real.pi * (min ((R - 1 / 2) / 2) (1 / 4)) ^ 2 ≤
        Real.pi * R ^ 2 := by
  simpa only [Erdos953OpenClosed.Mopen_eq_M] using
    Erdos953Defect.explicit_area_defect hR

/-- The full intersection of a disk with its unit translate gives a sharper
bound in the range where the translated intersections are disjoint. -/
theorem lens_area_defect_open {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (v : Plane) (hv : ‖v‖ = 1) :
    Erdos953OpenClosed.Mopen R +
      area (Metric.ball (0 : Plane) R ∩ Metric.ball (-v) R) ≤
        Real.pi * R ^ 2 := by
  simpa only [Erdos953OpenClosed.Mopen_eq_M] using
    Erdos953Defect.lens_area_defect hR0 hR1 v hv

/-- An explicit consequence of the lens bound, valid for `1/2 < R ≤ 1`. -/
theorem strong_explicit_area_defect_open {R : ℝ}
    (hR : 1 / 2 < R) (hR1 : R ≤ 1) :
    Erdos953OpenClosed.Mopen R +
      Real.pi * (R - 1 / 2) ^ 2 ≤ Real.pi * R ^ 2 := by
  simpa only [Erdos953OpenClosed.Mopen_eq_M] using
    Erdos953Defect.strong_explicit_area_defect hR hR1

/-- The full disk area is attainable as the supremum exactly through the
half-unit threshold. -/
theorem Mopen_eq_disk_area_iff_le_half (R : ℝ) (hR0 : 0 ≤ R) :
    Erdos953OpenClosed.Mopen R = Real.pi * R ^ 2 ↔ R ≤ 1 / 2 := by
  constructor
  · intro heq
    by_contra hnot
    have hgt : 1 / 2 < R := lt_of_not_ge hnot
    obtain ⟨δ, hδ, hgap⟩ := Erdos953Defect.exists_strict_area_defect hgt
    rw [← Erdos953OpenClosed.Mopen_eq_M R, heq] at hgap
    linarith
  · intro hle
    exact Mopen_eq_pi_mul_sq_of_le_half R hR0 hle

end Erdos953Sandwich

#print axioms Erdos953Sandwich.growth_sandwich
#print axioms Erdos953Sandwich.lower_polylog_for_Mopen
#print axioms Erdos953Sandwich.polylog_sandwich_open
#print axioms Erdos953Sandwich.growth_sandwich_open
#print axioms Erdos953Sandwich.Mopen_eq_pi_mul_sq_of_le_half
#print axioms Erdos953Sandwich.explicit_area_defect_open
#print axioms Erdos953Sandwich.lens_area_defect_open
#print axioms Erdos953Sandwich.strong_explicit_area_defect_open
#print axioms Erdos953Sandwich.Mopen_eq_disk_area_iff_le_half
#print axioms Erdos953Formalization.erdos953_upper
#print axioms Erdos953Lower.erdos953_lower
