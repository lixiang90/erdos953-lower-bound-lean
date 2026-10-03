import Erdos953Lower.AnisotropicUniform
import Erdos953Lower.Extremal
import Erdos953Sandwich

/-!
An explicit lower bound with coefficient 1/(32768 sqrt 10), for every
radius at least exp 1, and a complete lower bound at every positive radius.
The finite union witnesses and all numerical logarithm certificates are
proved in Lean; no externally computed comparison is an assumption.
-/

noncomputable section
namespace Erdos953SharpLower
open MeasureTheory Erdos953Lower Erdos953Formalization
set_option maxHeartbeats 400000

/-- The exact thin-rectangle construction, as a lower bound for open disks. -/
theorem digit_rectangle_lower (R : ℝ) (n k : ℕ) (hk : 3 ≤ k)
    (hfit : 10 * (k : ℝ) ^ (2 * n) ≤ R) :
    ((k : ℝ) - 1) ^ n / (1024 * (k : ℝ) ^ 3) ≤ Erdos953OpenClosed.Mopen R := by
  have hsub : digitRectangles k n ⊆ Metric.ball (0 : Erdos953Lower.Plane) R :=
    (digitRectangles_subset_ball k n hk).trans (Metric.ball_subset_ball hfit)
  have hA : AdmissibleSet R (digitRectangles k n) :=
    ⟨digitRectangles_measurable k n, hsub.trans Metric.ball_subset_closedBall,
      digitRectangles_no_positive_integer_distances k n hk⟩
  rw [Erdos953OpenClosed.Mopen_eq_M]
  simpa only [Erdos953Formalization.area, digitRectangles_area k n hk] using
    Erdos953Sandwich.area_le_M_of_admissible hA

/-- A measurable witness for the uniform logarithmic bound at large radii. -/
theorem large_radius_witness (R : ℝ) (hR : 100000000000000 ≤ R) :
    ∃ A : Set Erdos953Lower.Plane,
      MeasurableSet A ∧ A ⊆ Metric.ball 0 R ∧
      NoPositiveIntegerDistances A ∧ sharpLower R ≤ (volume A).toReal := by
  obtain ⟨n, k, hn2, hk, hnk, hfit, hgrid, hkbound⟩ :=
    choose_uniform_anisotropic_parameters R hR
  have hR0 : 0 < R := by linarith only [hR]
  have hT18 := log_radius_ge_eighteen R (by linarith only [hR])
  have hT0 : 0 < Real.log R := by linarith only [hT18]
  have hz0 : 0 < Real.log (Real.log R) := Real.log_pos (by linarith only [hT18])
  have hK0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let q : ℝ := Real.log (Real.log R) / Real.log R
  let s : ℝ := Real.sqrt (R / 10)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hkq : (k : ℝ) * q ≤ 2 := by
    have hcross := (lt_div_iff₀ hz0).1 hkbound
    have h : (k : ℝ) * Real.log (Real.log R) / Real.log R < 2 :=
      (div_lt_iff₀ hT0).2 hcross
    simpa only [q, mul_div_assoc] using h.le
  have hfac : ((k : ℝ) * q / 2) ^ 3 ≤ 1 := by
    have hbase : (k : ℝ) * q / 2 ≤ 1 := by linarith only [hkq]
    simpa only [one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ (k : ℝ) * q / 2) hbase 3
  have hidentity : s / 32768 * q ^ 3 =
      s / (4096 * (k : ℝ) ^ 3) * ((k : ℝ) * q / 2) ^ 3 := by
    field_simp [hK0.ne']
    ring
  have hscaled : s / 32768 * q ^ 3 ≤ s / (4096 * (k : ℝ) ^ 3) := by
    rw [hidentity]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac
      (by positivity : 0 ≤ s / (4096 * (k : ℝ) ^ 3))
  have hcount := anisotropic_digit_count_lower (R / 10) (k : ℝ) n
    (by positivity) (by exact_mod_cast (by omega : 1 ≤ k))
    (by exact_mod_cast hnk) hgrid
  have hdiv := div_lt_div_of_pos_right hcount
    (by positivity : (0 : ℝ) < 1024 * (k : ℝ) ^ 3)
  have hid : (Real.sqrt (R / 10) / 4) / (1024 * (k : ℝ) ^ 3) =
      s / (4096 * (k : ℝ) ^ 3) := by dsimp [s]; ring
  rw [hid] at hdiv
  refine ⟨digitRectangles k n, digitRectangles_measurable k n, ?_,
    digitRectangles_no_positive_integer_distances k n hk, ?_⟩
  · exact (digitRectangles_subset_ball k n hk).trans
      (Metric.ball_subset_ball (by linarith only [hfit]))
  · rw [digitRectangles_area k n hk]
    exact hscaled.trans hdiv.le

theorem extremal_area_mono {R S : ℝ} (hRS : R ≤ S) : M R ≤ M S := by
  apply M_le_of_admissible_area_bound
  intro A hA
  apply Erdos953Sandwich.area_le_M_of_admissible
  exact ⟨hA.1, hA.2.1.trans (Metric.closedBall_subset_closedBall hRS), hA.2.2⟩

theorem quarter_pi_lower (R : ℝ) (hR : 1 / 2 ≤ R) : Real.pi / 4 ≤ M R := by
  have hhalf := Erdos953SmallRadius.M_eq_pi_mul_sq_of_le_half
    (1 / 2) (by norm_num) (by norm_num)
  have heq : M (1 / 2) = Real.pi / 4 := by nlinarith only [hhalf]
  rw [← heq]
  exact extremal_area_mono hR

/-- The explicit coefficient in the original open-disk extremal formulation. -/
theorem sharp_lower_Mopen (R : ℝ) (hR : Real.exp 1 ≤ R) :
    ((1 : ℝ) / (32768 * Real.sqrt 10)) * Real.sqrt R *
      (Real.log (Real.log R) / Real.log R) ^ 3 ≤ Erdos953OpenClosed.Mopen R := by
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have hhalf : 1 / 2 ≤ R := by linarith only [Real.exp_one_gt_two, hR]
  have hlower : sharpLower R ≤ M R := by
    by_cases hlarge : 100000000000000 ≤ R
    · obtain ⟨A, hmeas, hsub, hno, harea⟩ := large_radius_witness R hlarge
      exact harea.trans (Erdos953Sandwich.area_le_M_of_admissible
        ⟨hmeas, hsub.trans Metric.ball_subset_closedBall, hno⟩)
    · exact (sharpLower_small_radius R hR (le_of_not_ge hlarge)).trans (quarter_pi_lower R hhalf)
  have hidentity : sharpLower R = ((1 : ℝ) / (32768 * Real.sqrt 10)) * Real.sqrt R *
      (Real.log (Real.log R) / Real.log R) ^ 3 := by
    unfold sharpLower
    rw [Real.sqrt_div hR0.le]
    ring
  rw [Erdos953OpenClosed.Mopen_eq_M, ← hidentity]
  exact hlower

def explicitLower (R : ℝ) : ℝ :=
  if R ≤ 1 / 2 then Real.pi * R ^ 2
  else if R < Real.exp 1 then Real.pi / 4
  else max (Real.pi / 4)
    (((1 : ℝ) / (32768 * Real.sqrt 10)) * Real.sqrt R *
      (Real.log (Real.log R) / Real.log R) ^ 3)

/-- The complete piecewise lower bound, at every positive real radius. -/
theorem explicit_lower_all_radii (R : ℝ) (hR : 0 < R) :
    explicitLower R ≤ Erdos953OpenClosed.Mopen R := by
  unfold explicitLower
  split_ifs with hhalf he
  · rw [Erdos953OpenClosed.Mopen_eq_M,
      Erdos953SmallRadius.M_eq_pi_mul_sq_of_le_half R hR.le hhalf]
  · rw [Erdos953OpenClosed.Mopen_eq_M]
    exact quarter_pi_lower R (le_of_not_ge hhalf)
  · apply max_le
    · rw [Erdos953OpenClosed.Mopen_eq_M]
      exact quarter_pi_lower R (le_of_not_ge hhalf)
    · exact sharp_lower_Mopen R (le_of_not_gt he)

theorem sharp_coefficient_pos : (0 : ℝ) < 1 / (32768 * Real.sqrt 10) := by
  positivity

/-- The identical theorem for the standalone extremal definition. -/
theorem sharp_lower_standalone (R : ℝ) (hR : Real.exp 1 ≤ R) :
    ((1 : ℝ) / (32768 * Real.sqrt 10)) * Real.sqrt R *
      (Real.log (Real.log R) / Real.log R) ^ 3 ≤ Erdos953Lower.Mopen R := by
  exact sharp_lower_Mopen R hR

theorem explicit_lower_standalone (R : ℝ) (hR : 0 < R) :
    explicitLower R ≤ Erdos953Lower.Mopen R := by
  exact explicit_lower_all_radii R hR

/-- An exact numerical construction, requiring no evaluation of logarithms. -/
theorem lower_at_ten_pow_eighteen :
    (170859375 / 4194304 : ℝ) ≤ Erdos953OpenClosed.Mopen ((10 : ℝ) ^ 18) := by
  have h := digit_rectangle_lower ((10 : ℝ) ^ 18) 7 16 (by norm_num) (by norm_num)
  norm_num at h
  norm_num
  exact h

#print axioms large_radius_witness
#print axioms sharp_lower_Mopen
#print axioms explicit_lower_all_radii
#print axioms sharp_lower_standalone
#print axioms explicit_lower_standalone
#print axioms lower_at_ten_pow_eighteen
end Erdos953SharpLower
