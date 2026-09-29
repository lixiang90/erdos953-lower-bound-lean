import Erdos953Formalization.MeasureReduction
import Erdos953Formalization.CircleBessel

/-!
An area-defect estimate for integer-distance-avoiding sets. The main lemma
encodes a translation matching between two disjoint measurable regions:
from every matched pair of points at unit distance, at least one point must
be omitted from the admissible set.
-/

noncomputable section

namespace Erdos953Defect

open Erdos953Formalization
open MeasureTheory
open scoped ENNReal

/-- A measurable pair of translated regions forces the forbidden-distance
set to miss at least the area of one region. -/
theorem area_add_le_of_unit_translation
    {A B U V : Set Plane} {v : Plane}
    (hAmeas : MeasurableSet A)
    (hAno : NoPositiveIntegerDistances A)
    (hAB : A ⊆ B)
    (hBfin : volume B < ∞)
    (hUmeas : MeasurableSet U)
    (hUV : Disjoint U V)
    (hUsub : U ⊆ B)
    (hVsub : V ⊆ B)
    (hV : V = (fun x : Plane => v + x) '' U)
    (hv : ‖v‖ = 1) :
    area A + area U ≤ area B := by
  let S : Set Plane := A ∩ U
  let T : Set Plane := (fun x : Plane => v + x) '' S
  have hTsubV : T ⊆ V := by
    rw [hV]
    exact Set.image_mono Set.inter_subset_right
  have hTsubAcompl : T ⊆ Aᶜ := by
    rintro y ⟨x, hx, rfl⟩ hy
    have hdist : dist x (v + x) = 1 := by
      calc
        dist x (v + x) = dist 0 v := by
          simpa using (dist_add_right (0 : Plane) v x)
        _ = 1 := by simpa [dist_eq_norm] using hv
    have hneq : x ≠ v + x := by
      intro heq
      have hzero : dist x (v + x) = 0 := by
        rw [← heq]
        exact dist_self x
      linarith
    exact hAno x hx.1 (v + x) hy hneq 1 (by norm_num)
      (by simpa using hdist)
  have hTsub : T ⊆ B \ A := by
    intro y hy
    exact ⟨hVsub (hTsubV hy), hTsubAcompl hy⟩
  have hUsub' : U \ A ⊆ B \ A := by
    intro x hx
    exact ⟨hUsub hx.1, hx.2⟩
  have hdisj : Disjoint (U \ A) T :=
    hUV.mono Set.sdiff_subset hTsubV
  have hvolT : volume T = volume S := by
    dsimp [T]
    rw [Set.image_add_left]
    exact measure_preimage_add (volume : Measure Plane) (-v) S
  have hUle : volume U ≤ volume (B \ A) := by
    calc
      volume U = volume S + volume (U \ A) := by
        simpa only [S, Set.inter_comm] using
          (measure_inter_add_sdiff U hAmeas).symm
      _ = volume T + volume (U \ A) := by rw [hvolT]
      _ = volume (U \ A) + volume T := add_comm _ _
      _ = volume ((U \ A) ∪ T) :=
        (measure_union' hdisj (hUmeas.diff hAmeas)).symm
      _ ≤ volume (B \ A) :=
        measure_mono (Set.union_subset hUsub' hTsub)
  have hvol : volume A + volume U ≤ volume B := by
    calc
      volume A + volume U ≤ volume A + volume (B \ A) :=
        add_le_add_right hUle _
      _ = volume B := by
        rw [measure_add_sdiff hAmeas.nullMeasurableSet]
        exact congrArg volume (Set.union_eq_right.mpr hAB)
  have hAfin : volume A ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hAB) hBfin)
  have hUfin : volume U ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hUsub) hBfin)
  calc
    area A + area U = (volume A + volume U).toReal := by
      simp only [area, ENNReal.toReal_add hAfin hUfin]
    _ ≤ (volume B).toReal := ENNReal.toReal_mono (ne_of_lt hBfin) hvol
    _ = area B := rfl

private def unitStep : Plane := CircleBessel.xAxisPoint 1
private def leftCenter : Plane := CircleBessel.xAxisPoint (-(1 / 2 : ℝ))
private def rightCenter : Plane := CircleBessel.xAxisPoint (1 / 2 : ℝ)

private lemma leftCenter_add_unitStep : leftCenter + unitStep = rightCenter := by
  ext i
  fin_cases i <;> simp [leftCenter, rightCenter, unitStep,
    CircleBessel.xAxisPoint] <;> ring

private lemma norm_unitStep : ‖unitStep‖ = 1 := by
  simpa [unitStep] using CircleBessel.norm_xAxisPoint (1 : ℝ)

private lemma norm_leftCenter : ‖leftCenter‖ = 1 / 2 := by
  simpa [leftCenter] using CircleBessel.norm_xAxisPoint (-(1 / 2 : ℝ))

private lemma norm_rightCenter : ‖rightCenter‖ = 1 / 2 := by
  simpa [rightCenter] using CircleBessel.norm_xAxisPoint (1 / 2 : ℝ)

private lemma dist_centers : dist leftCenter rightCenter = 1 := by
  rw [← leftCenter_add_unitStep]
  simpa [dist_eq_norm] using norm_unitStep

private lemma ball_right_eq_translate (ρ : ℝ) :
    Metric.ball rightCenter ρ =
      (fun x : Plane => unitStep + x) '' Metric.ball leftCenter ρ := by
  ext y
  constructor
  · intro hy
    refine ⟨y - unitStep, ?_, by abel⟩
    have heq : unitStep + (y - unitStep) = y := by abel
    have hdist : dist (unitStep + (y - unitStep))
        (unitStep + leftCenter) < ρ := by
      simpa [heq, add_comm, leftCenter_add_unitStep] using
        (Metric.mem_ball.mp hy)
    exact Metric.mem_ball.mpr (by simpa only [dist_add_left] using hdist)
  · rintro ⟨x, hx, rfl⟩
    apply Metric.mem_ball.mpr
    rw [← leftCenter_add_unitStep, add_comm leftCenter unitStep,
      dist_add_left]
    exact Metric.mem_ball.mp hx

private lemma area_ball_eq_pi_mul_sq (x : Plane) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    area (Metric.ball x ρ) = Real.pi * ρ ^ 2 := by
  have hsame : area (Metric.ball x ρ) = area (Metric.closedBall x ρ) := by
    simp [area]
  rw [hsame, area_closedBall_plane_eq_pi_mul_sq x hρ]

/-- For radii at most one, the entire overlap of a disk with its unit
translate can be paired without double-counting. This gives a stronger
area defect than pairing two small balls. -/
theorem lens_area_defect {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (v : Plane) (hv : ‖v‖ = 1) :
    M R + area (Metric.ball (0 : Plane) R ∩ Metric.ball (-v) R) ≤
      Real.pi * R ^ 2 := by
  let U : Set Plane := Metric.ball 0 R ∩ Metric.ball (-v) R
  let V : Set Plane := (fun x : Plane => v + x) '' U
  let B : Set Plane := Metric.closedBall 0 R
  have hUmeas : MeasurableSet U := measurableSet_ball.inter measurableSet_ball
  have hUsub : U ⊆ B := by
    intro x hx
    exact Metric.ball_subset_closedBall hx.1
  have hVsub : V ⊆ B := by
    rintro y ⟨x, hx, rfl⟩
    have hdist : dist (v + x) (0 : Plane) = dist x (-v) := by
      simpa using (dist_add_left v x (-v))
    exact Metric.mem_closedBall.mpr (by
      rw [hdist]
      exact (Metric.mem_ball.mp hx.2).le)
  have hVinRight : V ⊆ Metric.ball v R := by
    rintro y ⟨x, hx, rfl⟩
    apply Metric.mem_ball.mpr
    have hdist : dist (v + x) v = dist x (0 : Plane) := by
      simpa using (dist_add_left v x (0 : Plane))
    rw [hdist]
    exact Metric.mem_ball.mp hx.1
  have hcenter : dist (-v) v = 2 := by
    have heq : (-v) - v = (-2 : ℝ) • v := by module
    rw [dist_eq_norm, heq, norm_smul, hv]
    norm_num
  have hballs : Disjoint (Metric.ball (-v) R) (Metric.ball v R) := by
    apply Metric.ball_disjoint_ball
    rw [hcenter]
    linarith
  have hUV : Disjoint U V := hballs.mono Set.inter_subset_right hVinRight
  have hareaB : area B = Real.pi * R ^ 2 :=
    area_closedBall_plane_eq_pi_mul_sq 0 hR0
  have hbound : ∀ A : Set Plane, AdmissibleSet R A →
      area A ≤ Real.pi * R ^ 2 - area U := by
    intro A hA
    have hpair := area_add_le_of_unit_translation
      hA.1 hA.noPositiveIntegerDistances hA.subset_closedBall
      (volume_closedBall_plane_lt_top 0 R)
      hUmeas hUV hUsub hVsub rfl hv
    rw [hareaB] at hpair
    linarith
  have hM := M_le_of_admissible_area_bound hbound
  change M R + area U ≤ Real.pi * R ^ 2
  linarith

/-- The lens contains a disk of radius `R - 1/2`; this converts its area
defect into a simple explicit estimate on the whole interval `(1/2, 1]`. -/
theorem strong_explicit_area_defect {R : ℝ} (hR : 1 / 2 < R)
    (hR1 : R ≤ 1) :
    M R + Real.pi * (R - 1 / 2) ^ 2 ≤ Real.pi * R ^ 2 := by
  let ρ : ℝ := R - 1 / 2
  have hρpos : 0 < ρ := by dsimp [ρ]; linarith
  have hsub : Metric.ball leftCenter ρ ⊆
      Metric.ball (0 : Plane) R ∩ Metric.ball (-unitStep) R := by
    intro x hx
    have hxρ : dist x leftCenter < ρ := Metric.mem_ball.mp hx
    dsimp [ρ] at hxρ
    constructor
    · apply Metric.mem_ball.mpr
      have hc : dist leftCenter (0 : Plane) = 1 / 2 := by
        simpa [dist_eq_norm] using norm_leftCenter
      have htri := dist_triangle x leftCenter (0 : Plane)
      linarith
    · apply Metric.mem_ball.mpr
      have hshift : dist (unitStep + x) (unitStep + leftCenter) =
          dist x leftCenter := dist_add_left _ _ _
      have hc : dist (unitStep + leftCenter) (0 : Plane) = 1 / 2 := by
        rw [show unitStep + leftCenter = rightCenter by
          simpa [add_comm] using leftCenter_add_unitStep]
        simpa [dist_eq_norm] using norm_rightCenter
      have htri := dist_triangle (unitStep + x)
        (unitStep + leftCenter) (0 : Plane)
      have hdist : dist x (-unitStep) = dist (unitStep + x) (0 : Plane) := by
        simpa using (dist_add_left unitStep x (-unitStep)).symm
      rw [hdist]
      linarith
  have hfin : volume (Metric.ball (0 : Plane) R ∩
      Metric.ball (-unitStep) R) < ∞ := by
    apply lt_of_le_of_lt (measure_mono
      (Set.inter_subset_left.trans Metric.ball_subset_closedBall))
    exact volume_closedBall_plane_lt_top 0 R
  have harea : Real.pi * ρ ^ 2 ≤
      area (Metric.ball (0 : Plane) R ∩ Metric.ball (-unitStep) R) := by
    rw [← area_ball_eq_pi_mul_sq leftCenter hρpos.le]
    exact area_mono_of_subset_of_finite hsub hfin
  have hlens := lens_area_defect (by linarith : 0 ≤ R)
    hR1 unitStep norm_unitStep
  change M R + Real.pi * ρ ^ 2 ≤ Real.pi * R ^ 2
  linarith

/-- As soon as the disk radius exceeds one half, a fixed pair of translated
positive-area balls forces an explicit uniform area defect. -/
theorem explicit_area_defect {R : ℝ} (hR : 1 / 2 < R) :
    M R + Real.pi * (min ((R - 1 / 2) / 2) (1 / 4)) ^ 2 ≤
      Real.pi * R ^ 2 := by
  let ρ : ℝ := min ((R - 1 / 2) / 2) (1 / 4)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by linarith) (by norm_num)
  have hρle1 : ρ ≤ (R - 1 / 2) / 2 := min_le_left _ _
  have hρle2 : ρ ≤ 1 / 4 := min_le_right _ _
  have hρR : ρ + 1 / 2 ≤ R := by linarith
  have hρdisj : ρ + ρ ≤ 1 := by linarith
  let U : Set Plane := Metric.ball leftCenter ρ
  let V : Set Plane := Metric.ball rightCenter ρ
  let B : Set Plane := Metric.closedBall (0 : Plane) R
  have hUsub : U ⊆ B := by
    intro x hx
    have hxρ : dist x leftCenter < ρ := Metric.mem_ball.mp hx
    have hc : dist leftCenter 0 = 1 / 2 := by
      simpa [dist_eq_norm] using norm_leftCenter
    have htri := dist_triangle x leftCenter 0
    exact Metric.mem_closedBall.mpr (by linarith)
  have hVsub : V ⊆ B := by
    intro x hx
    have hxρ : dist x rightCenter < ρ := Metric.mem_ball.mp hx
    have hc : dist rightCenter 0 = 1 / 2 := by
      simpa [dist_eq_norm] using norm_rightCenter
    have htri := dist_triangle x rightCenter 0
    exact Metric.mem_closedBall.mpr (by linarith)
  have hUV : Disjoint U V := by
    apply Metric.ball_disjoint_ball
    rw [dist_centers]
    exact hρdisj
  have hV : V = (fun x : Plane => unitStep + x) '' U :=
    ball_right_eq_translate ρ
  have hareaU : area U = Real.pi * ρ ^ 2 :=
    area_ball_eq_pi_mul_sq leftCenter hρpos.le
  have hareaB : area B = Real.pi * R ^ 2 :=
    area_closedBall_plane_eq_pi_mul_sq 0 (by linarith)
  have hbound : ∀ A : Set Plane, AdmissibleSet R A →
      area A ≤ Real.pi * R ^ 2 - Real.pi * ρ ^ 2 := by
    intro A hA
    have hpair := area_add_le_of_unit_translation
      hA.1 hA.noPositiveIntegerDistances hA.subset_closedBall
      (volume_closedBall_plane_lt_top 0 R)
      (show MeasurableSet U from measurableSet_ball)
      hUV hUsub hVsub hV norm_unitStep
    rw [hareaU, hareaB] at hpair
    linarith
  have hM := M_le_of_admissible_area_bound hbound
  change M R + Real.pi * ρ ^ 2 ≤ Real.pi * R ^ 2
  linarith

theorem exists_strict_area_defect {R : ℝ} (hR : 1 / 2 < R) :
    ∃ δ : ℝ, 0 < δ ∧ M R + δ ≤ Real.pi * R ^ 2 := by
  let ρ : ℝ := min ((R - 1 / 2) / 2) (1 / 4)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by linarith) (by norm_num)
  refine ⟨Real.pi * ρ ^ 2, by positivity, ?_⟩
  exact explicit_area_defect hR

end Erdos953Defect

#print axioms Erdos953Defect.area_add_le_of_unit_translation
#print axioms Erdos953Defect.lens_area_defect
#print axioms Erdos953Defect.strong_explicit_area_defect
#print axioms Erdos953Defect.explicit_area_defect
#print axioms Erdos953Defect.exists_strict_area_defect
