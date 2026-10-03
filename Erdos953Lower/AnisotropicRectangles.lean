import Erdos953Lower.AnisotropicDigits
import Erdos953Lower.AnisotropicRadius
import Erdos953Lower.Thickening
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Erdos953Lower
open MeasureTheory
noncomputable section
set_option maxHeartbeats 300000

def rectangleHeight (k : ℕ) : ℝ := 1 / (256 * (k : ℝ) ^ 3)

def thinRectangle (p : Plane) (ε : ℝ) : Set Plane :=
  {x | |x 0 - p 0| < 1 / 8 ∧ |x 1 - p 1| < ε / 2}

def digitRectangles (k n : ℕ) : Set Plane :=
  ⋃ α : Fin n → Fin (k - 1), thinRectangle (digitPoint k n α) (rectangleHeight k)

theorem plane_dist_coordinates (x y : Plane) :
    dist x y = Real.sqrt ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem coordinate_perturbation (x y p q r : ℝ)
    (hx : |x - p| < r) (hy : |y - q| < r) :
    abs (abs (x - y) - abs (p - q)) < 2 * r := by
  calc
    abs (abs (x - y) - abs (p - q)) ≤ |(x - y) - (p - q)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ = |(x - p) - (y - q)| := by congr 1; ring
    _ ≤ |x - p| + |y - q| := abs_sub _ _
    _ < 2 * r := by linarith

theorem thinRectangle_measurable (p : Plane) (ε : ℝ) :
    MeasurableSet (thinRectangle p ε) := by
  have h0 : Continuous (fun x : Plane => x 0) := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous (fun x : Plane => x 1) := PiLp.continuous_apply 2 _ 1
  exact ((isOpen_lt (h0.sub continuous_const).abs continuous_const).inter
    (isOpen_lt (h1.sub continuous_const).abs continuous_const)).measurableSet

theorem thinRectangle_volume (p : Plane) (ε : ℝ) :
    volume (thinRectangle p ε) = ENNReal.ofReal (ε / 4) := by
  let h : Fin 2 → ℝ := fun i => if i = 0 then 1 / 8 else ε / 2
  have hpre : WithLp.toLp 2 ⁻¹' thinRectangle p ε =
      Set.pi Set.univ (fun i => Set.Ioo (p i - h i) (p i + h i)) := by
    ext x
    simp only [Set.mem_preimage, thinRectangle, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, forall_const, Fin.forall_fin_two, Set.mem_Ioo]
    dsimp [h]
    simp only [abs_lt]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    (thinRectangle_measurable p ε).nullMeasurableSet, hpre, Real.volume_pi_Ioo]
  simp only [Fin.prod_univ_two]
  dsimp [h]
  have h0 : p 0 + 1 / 8 - (p 0 - 1 / 8) = (1 / 4 : ℝ) := by ring
  have h1 : p 1 + ε / 2 - (p 1 - ε / 2) = ε := by ring
  rw [h0, h1, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  congr 1
  ring

theorem rectangleHeight_bounds (k : ℕ) (hk : 3 ≤ k) :
    0 < rectangleHeight k ∧ rectangleHeight k ≤ 1 / 16 := by
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hpow : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hK
  have hden : (0 : ℝ) < 256 * (k : ℝ) ^ 3 := by positivity
  refine ⟨by unfold rectangleHeight; positivity, ?_⟩
  unfold rectangleHeight
  apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 16)).2
  nlinarith only [hpow]

theorem thinRectangle_diameter (p : Plane) (ε : ℝ) (hε : ε ≤ 1 / 16)
    {x y : Plane} (hx : x ∈ thinRectangle p ε) (hy : y ∈ thinRectangle p ε) :
    dist x y < 1 := by
  have h0 := coordinate_perturbation (x 0) (y 0) (p 0) (p 0) (1 / 8) hx.1 hy.1
  have h1 := coordinate_perturbation (x 1) (y 1) (p 1) (p 1) (ε / 2) hx.2 hy.2
  simp only [sub_self, abs_zero, sub_zero, abs_abs] at h0 h1
  have hx0 := abs_nonneg (x 0 - y 0)
  have hx1 := abs_nonneg (x 1 - y 1)
  have hs0 := Real.sqrt_nonneg ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2)
  have hs2 := Real.sq_sqrt (show 0 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 by positivity)
  rw [plane_dist_coordinates]
  have hsq0 : (x 0 - y 0) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    nlinarith only [h0, hx0, sq_abs (x 0 - y 0)]
  have hsq1 : (x 1 - y 1) ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by
    nlinarith only [h1, hx1, hε, sq_abs (x 1 - y 1)]
  nlinarith only [hs0, hs2, hsq0, hsq1]

theorem digitRectangle_cross_gap (k n : ℕ) (hk : 3 ≤ k)
    (α β : Fin n → Fin (k - 1)) (hab : α ≠ β)
    {x y : Plane}
    (hx : x ∈ thinRectangle (digitPoint k n α) (rectangleHeight k))
    (hy : y ∈ thinRectangle (digitPoint k n β) (rectangleHeight k)) :
    ∀ z : ℤ, rectangleHeight k < |dist x y - (z : ℝ)| := by
  let A : ℤ := |yCoord k n α - yCoord k n β|
  let B : ℤ := |xCoord k n α - xCoord k n β|
  have hrat := digitPoint_coordinate_ratios k n hk α β hab
  change 1 ≤ A ∧ 1 ≤ B ∧ (B : ℝ) ^ 2 ≤ (A : ℝ) ∧
    (A : ℝ) ≤ 16 * (k : ℝ) ^ 3 * (B : ℝ) ^ 2 at hrat
  have ha : |digitPoint k n α 1 - digitPoint k n β 1| = (A : ℝ) := by
    simp [A, Int.cast_abs, Int.cast_sub]
  have hb : |digitPoint k n α 0 - digitPoint k n β 0| = (B : ℝ) := by
    simp [B, Int.cast_abs, Int.cast_sub]
  let u := |x 0 - y 0| - (B : ℝ)
  let v := |x 1 - y 1| - (A : ℝ)
  have hu : |u| ≤ 1 / 4 := by
    have h := coordinate_perturbation _ _ _ _ _ hx.1 hy.1
    rw [hb] at h
    dsimp [u]
    linarith only [h]
  have hv : |v| ≤ rectangleHeight k := by
    have h := coordinate_perturbation _ _ _ _ _ hx.2 hy.2
    rw [ha] at h
    dsimp [v]
    linarith only [h]
  have hK0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hquot : (A : ℝ) / (16 * (k : ℝ) ^ 3) ≤ (B : ℝ) ^ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (k : ℝ) ^ 3)).2
    nlinarith only [hrat.2.2.2]
  have hlow : 16 * (A : ℝ) * rectangleHeight k ≤ (B : ℝ) ^ 2 := by
    convert hquot using 1
    unfold rectangleHeight
    ring
  have hg := anisotropic_distance_gap A (B : ℝ) (rectangleHeight k) u v
    (by exact_mod_cast hrat.1) (by exact_mod_cast hrat.2.1)
    (rectangleHeight_bounds k hk).1 (rectangleHeight_bounds k hk).2
    hlow hrat.2.2.1 hu hv
  have heq : Real.sqrt (((A : ℝ) + v) ^ 2 + ((B : ℝ) + u) ^ 2) = dist x y := by
    rw [plane_dist_coordinates]
    dsimp [u, v]
    congr 1
    simp only [add_sub_cancel, sq_abs]
    ring
  simpa only [heq] using hg

theorem digitRectangles_measurable (k n : ℕ) : MeasurableSet (digitRectangles k n) := by
  exact MeasurableSet.iUnion (fun _ => thinRectangle_measurable _ _)

theorem digitRectangles_no_positive_integer_distances (k n : ℕ) (hk : 3 ≤ k) :
    ∀ x ∈ digitRectangles k n, ∀ y ∈ digitRectangles k n, x ≠ y →
      ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ) := by
  intro x hx y hy _ m hm heq
  obtain ⟨α, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨β, hy⟩ := Set.mem_iUnion.mp hy
  by_cases hab : α = β
  · subst β
    have hdist := thinRectangle_diameter _ _ (rectangleHeight_bounds k hk).2 hx hy
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hdist, heq, hm1]
  · have hdist := digitRectangle_cross_gap k n hk α β hab hx hy (m : ℤ)
    have hpos := (rectangleHeight_bounds k hk).1
    simp only [Int.cast_natCast, heq, sub_self, abs_zero] at hdist
    linarith only [hpos, hdist]

theorem digitRectangles_pairwiseDisjoint (k n : ℕ) (hk : 3 ≤ k) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin n → Fin (k - 1)))
      (fun α => thinRectangle (digitPoint k n α) (rectangleHeight k)) := by
  intro α _ β _ hab
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h := coordinate_perturbation (x 0) (x 0)
    (digitPoint k n α 0) (digitPoint k n β 0) (1 / 8) hx.1 hy.1
  have hrat := (digitPoint_coordinate_ratios k n hk α β hab).2.1
  have hrat' : (1 : ℝ) ≤ |digitPoint k n α 0 - digitPoint k n β 0| := by
    simpa [Int.cast_abs, Int.cast_sub] using (show (1 : ℝ) ≤
      (|xCoord k n α - xCoord k n β| : ℤ) by exact_mod_cast hrat)
  simp only [sub_self, abs_zero, zero_sub, abs_neg, abs_abs] at h
  linarith only [h, hrat']

theorem digitRectangles_volume (k n : ℕ) (hk : 3 ≤ k) :
    volume (digitRectangles k n) =
      (((k - 1) ^ n : ℕ) : ENNReal) * ENNReal.ofReal (rectangleHeight k / 4) := by
  classical
  have hd : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin n → Fin (k - 1))))
      (fun α => thinRectangle (digitPoint k n α) (rectangleHeight k)) := by
    simpa only [Finset.coe_univ] using digitRectangles_pairwiseDisjoint k n hk
  have hv := measure_biUnion_finset (μ := volume) hd
    (fun _ _ => thinRectangle_measurable _ _)
  simpa [digitRectangles, thinRectangle_volume, Fintype.card_fun] using hv

theorem digitRectangles_area (k n : ℕ) (hk : 3 ≤ k) :
    (volume (digitRectangles k n)).toReal =
      ((k : ℝ) - 1) ^ n / (1024 * (k : ℝ) ^ 3) := by
  rw [digitRectangles_volume k n hk, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by
      exact div_nonneg (rectangleHeight_bounds k hk).1.le (by norm_num))]
  have hcast : (((k - 1) ^ n : ℕ) : ℝ) = ((k : ℝ) - 1) ^ n := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  rw [hcast]
  unfold rectangleHeight
  ring

theorem digitRectangles_subset_ball (k n : ℕ) (hk : 3 ≤ k) :
    digitRectangles k n ⊆ Metric.ball (0 : Plane) (10 * (k : ℝ) ^ (2 * n)) := by
  intro x hx
  obtain ⟨α, hx⟩ := Set.mem_iUnion.mp hx
  have hp : digitPoint k n α ∈ thinRectangle (digitPoint k n α) (rectangleHeight k) := by
    constructor
    · simp only [sub_self, abs_zero]
      norm_num
    · simp only [sub_self, abs_zero]
      positivity [(rectangleHeight_bounds k hk).1]
  have hdist := thinRectangle_diameter _ _ (rectangleHeight_bounds k hk).2 hx hp
  have hcenter := digitPoint_radius_sharp k n hk α
  have hpow : ((k : ℝ) ^ 2) ^ n = (k : ℝ) ^ (2 * n) := by rw [pow_mul]
  rw [hpow] at hcenter
  have hbase : (1 : ℝ) ≤ (k : ℝ) ^ (2 * n) :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ k))
  apply Metric.mem_ball.mpr
  calc
    dist x 0 ≤ dist x (digitPoint k n α) + dist (digitPoint k n α) 0 :=
      dist_triangle _ _ _
    _ < 10 * (k : ℝ) ^ (2 * n) := by linarith only [hdist, hcenter, hbase]

#print axioms digitRectangles_no_positive_integer_distances
#print axioms digitRectangles_area
#print axioms digitRectangles_subset_ball

end
end Erdos953Lower
