import Erdos953Lower.RetreatAssembly
import Erdos953Lower.RetreatUniform
import Erdos953Lower.Extremal

/-! A single fixed infinite open set, with the coefficient 9/9604
for every real radius R >= exp 1. No upper-bound project is imported. -/
namespace Erdos953Lower
open MeasureTheory
noncomputable section
set_option maxHeartbeats 1000000

def retreatLocalArea (R : ℝ) : ℝ := (volume (retreatInfinity ∩ Metric.ball (0 : Plane) R)).toReal

theorem retreatLocalArea_finite (R : ℝ) :
    volume (retreatInfinity ∩ Metric.ball (0 : Plane) R) ≠ ⊤ := by
  have hh : volume (Metric.closedBall (0 : Plane) R) < ⊤ := by
    rw [EuclideanSpace.volume_closedBall]
    finiteness
  exact ne_of_lt ((measure_mono (Set.inter_subset_right.trans Metric.ball_subset_closedBall)).trans_lt hh)

theorem retreatLocalArea_base (R : ℝ) (hR : 1 ≤ R) : 3/8 ≤ retreatLocalArea R := by
  have hsub : retreatBase ⊆ retreatInfinity ∩ Metric.ball (0 : Plane) R := by
    intro x hx
    exact ⟨Or.inl hx,(Metric.ball_subset_ball hR) (retreatBase_subset_unit_ball hx)⟩
  have hh := ENNReal.toReal_mono (retreatLocalArea_finite R) (measure_mono hsub)
  rw [retreatBase_volume,ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3/8)] at hh
  exact hh

theorem retreatLocalArea_generation (j : ℕ) (hj : 14 ≤ j) (R : ℝ)
    (hR : generationRadius j ≤ R) :
    retreatGain*referenceArea (tailParameters j hj).k (tailParameters j hj).n ≤ retreatLocalArea R := by
  have hsub : tailGeneration j hj ⊆ retreatInfinity ∩ Metric.ball (0 : Plane) R := by
    intro x hx
    refine ⟨Or.inr (Set.mem_iUnion.mpr ⟨⟨j,hj⟩,hx⟩),?_⟩
    exact (Metric.ball_subset_ball hR) (tailGeneration_subset_ball j hj hx)
  have hh := ENNReal.toReal_mono (retreatLocalArea_finite R) (measure_mono hsub)
  rw [tailGeneration_volume] at hh
  let P := tailParameters j hj
  let t := tailTrim j hj
  have ht := tailTrim_spec j hj
  have hk := retreat_parameter_k_ge_eight P hj
  change 1 ≤ t ∧ 2*t ≤ P.k at ht
  have harea0 : 0 ≤ retreatArea P.k P.n t := by
    have hcast : (t : ℝ) ≤ P.k := by exact_mod_cast (by omega : t ≤ P.k)
    have hkt : (0 : ℝ) ≤ (P.k : ℝ)-t := sub_nonneg.mpr hcast
    unfold retreatArea
    positivity [(retreatHeight_bounds P.k t hk ht.1).1]
  rw [ENNReal.toReal_ofReal harea0] at hh
  exact (optimalTrim_gain P.k P.n hk P.hnk).trans hh

theorem retreatLower_small (R : ℝ) (hR : Real.exp 1 ≤ R) (hmax : R ≤ 16384) :
    retreatLower R ≤ 3/8 := by
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have hT1 : 1 ≤ Real.log R := (Real.le_log_iff_exp_le hR0).2 hR
  have hT0 : 0 < Real.log R := by linarith
  have hq0 : 0 ≤ radiusQuotient R := by
    unfold radiusQuotient
    exact div_nonneg (Real.log_nonneg hT1) hT0.le
  have hq1 : radiusQuotient R ≤ 1 := by
    unfold radiusQuotient
    apply (div_le_one hT0).2
    exact Real.log_le_self hT0.le
  have hs0 := Real.sqrt_nonneg R
  have hs2 := Real.sq_sqrt hR0.le
  have hs : Real.sqrt R ≤ 128 := by nlinarith only [hs0,hs2,hmax]
  have hqpow : (radiusQuotient R)^3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hq0 hq1 3
  have hprod := mul_le_mul hs hqpow (pow_nonneg hq0 3) (by norm_num : (0 : ℝ) ≤ 128)
  unfold retreatLower
  nlinarith only [hprod]

/-- Full fixed-set lower bound, for every real radius >= e. -/
theorem retreatInfinity_uniform_lower (R : ℝ) (hR : Real.exp 1 ≤ R) :
    (9/9604 : ℝ)*Real.sqrt R*(Real.log (Real.log R)/Real.log R)^3 ≤
      (volume (retreatInfinity ∩ Metric.ball (0 : Plane) R)).toReal := by
  change retreatLower R ≤ retreatLocalArea R
  have hR1 : 1 ≤ R := by linarith only [Real.exp_one_gt_two,hR]
  by_cases hlarge : 16384 ≤ R
  · obtain ⟨j,hj,hfit,hnext⟩ := complete_generation_for_radius R hlarge
    by_cases hj14 : 14 ≤ j
    · exact (retreatLower_for_generation (tailParameters j hj14) hj R hfit hnext).trans
        (retreatLocalArea_generation j hj14 R hfit)
    · let P := chosenParameters j hj
      exact (retreatLower_for_generation P hj R hfit hnext).trans
        ((early_prefix_area P hj (by omega)).trans (retreatLocalArea_base R hR1))
  · exact (retreatLower_small R hR (le_of_not_ge hlarge)).trans (retreatLocalArea_base R hR1)

theorem retreat_lower_Mopen (R : ℝ) (hR : Real.exp 1 ≤ R) :
    (9/9604 : ℝ)*Real.sqrt R*(Real.log (Real.log R)/Real.log R)^3 ≤ Mopen R := by
  apply (retreatInfinity_uniform_lower R hR).trans
  apply area_le_Mopen_of_admissible
  refine ⟨retreatInfinity_measurable.inter Metric.isOpen_ball.measurableSet,Set.inter_subset_right,?_⟩
  intro x hx y hy _ m hm
  exact retreatInfinity_no_integer x hx.1 y hy.1 m hm

/-- The paper's fixed, unbounded, open witness and its full uniform bound. -/
theorem fixed_unbounded_uniform_lower :
    ∃ A : Set Plane, IsOpen A ∧ (∀ R : ℝ, ∃ x ∈ A, R < dist x 0) ∧
      (∀ x ∈ A, ∀ y ∈ A, ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ)) ∧
      ∀ R : ℝ, Real.exp 1 ≤ R →
        (9/9604 : ℝ)*Real.sqrt R*(Real.log (Real.log R)/Real.log R)^3 ≤
          (volume (A ∩ Metric.ball (0 : Plane) R)).toReal :=
  ⟨retreatInfinity,retreatInfinity_isOpen,retreatInfinity_unbounded,
    retreatInfinity_no_integer,retreatInfinity_uniform_lower⟩

#print axioms fixed_unbounded_uniform_lower
#print axioms retreatInfinity_uniform_lower
#print axioms retreat_lower_Mopen
end
end Erdos953Lower
