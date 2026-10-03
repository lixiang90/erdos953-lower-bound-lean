/-
  Explicit two-lobe constructions in a disk of half-integer radius.
  This file formalizes measurability, containment, and avoidance of every
  positive integer distance. The exact area formula is in the research note;
  its integration and the restricted-family optimality are not formalized here.
-/
import Erdos953Lower.Extremal

namespace Erdos953Lower.SmallRadiusLobes

open MeasureTheory
noncomputable section
set_option maxHeartbeats 50000

def axisCenter (c : ℝ) : Plane := !₂[c, 0]

def rightLobe (R c t : ℝ) : Set Plane :=
  (Metric.ball 0 R ∩ Metric.ball (axisCenter c) (1 / 2)) ∩ {p | t < p 0}

def leftLobe (R c t : ℝ) : Set Plane :=
  (Metric.ball 0 R ∩ Metric.ball (axisCenter (-c)) (1 / 2)) ∩ {p | p 0 < -t}

def lobes (R c t : ℝ) : Set Plane := rightLobe R c t ∪ leftLobe R c t

lemma coordinate_sub_le_dist (p q : Plane) : |p 0 - q 0| ≤ dist p q := by
  have h := PiLp.norm_apply_le (p - q) (0 : Fin 2)
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, dist_eq_norm] using h

lemma rightLobe_isOpen (R c t : ℝ) : IsOpen (rightLobe R c t) := by
  have hcoord : Continuous (fun p : Plane => p 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  exact (Metric.isOpen_ball.inter Metric.isOpen_ball).inter
    (isOpen_lt continuous_const hcoord)

lemma leftLobe_isOpen (R c t : ℝ) : IsOpen (leftLobe R c t) := by
  have hcoord : Continuous (fun p : Plane => p 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  exact (Metric.isOpen_ball.inter Metric.isOpen_ball).inter
    (isOpen_lt hcoord continuous_const)

theorem lobes_isOpen (R c t : ℝ) : IsOpen (lobes R c t) :=
  (rightLobe_isOpen R c t).union (leftLobe_isOpen R c t)

lemma rightLobe_dist_lt_one {R c t : ℝ} {p q : Plane}
    (hp : p ∈ rightLobe R c t) (hq : q ∈ rightLobe R c t) :
    dist p q < 1 := by
  have hp' : dist p (axisCenter c) < 1 / 2 := Metric.mem_ball.mp hp.1.2
  have hq' : dist (axisCenter c) q < 1 / 2 := by
    simpa only [dist_comm] using Metric.mem_ball.mp hq.1.2
  have htri := dist_triangle p (axisCenter c) q
  linarith only [hp', hq', htri]

lemma leftLobe_dist_lt_one {R c t : ℝ} {p q : Plane}
    (hp : p ∈ leftLobe R c t) (hq : q ∈ leftLobe R c t) :
    dist p q < 1 := by
  have hp' : dist p (axisCenter (-c)) < 1 / 2 := Metric.mem_ball.mp hp.1.2
  have hq' : dist (axisCenter (-c)) q < 1 / 2 := by
    simpa only [dist_comm] using Metric.mem_ball.mp hq.1.2
  have htri := dist_triangle p (axisCenter (-c)) q
  linarith only [hp', hq', htri]

/-- For `2R≤m` and `2t=m-1`, all cross-lobe distances are in `(m-1,m)`. -/
theorem cross_lobe_distance_between (R c t : ℝ) (m : ℕ)
    (hR : 2 * R ≤ (m : ℝ)) (ht : 2 * t = (m : ℝ) - 1)
    {p q : Plane} (hp : p ∈ rightLobe R c t) (hq : q ∈ leftLobe R c t) :
    (m : ℝ) - 1 < dist p q ∧ dist p q < (m : ℝ) := by
  have hp₀ : t < p 0 := hp.2
  have hq₀ : q 0 < -t := hq.2
  have hcoord := coordinate_sub_le_dist p q
  have habs := le_abs_self (p 0 - q 0)
  have hpR : dist p 0 < R := Metric.mem_ball.mp hp.1.1
  have hqR : dist (0 : Plane) q < R := by
    simpa only [dist_comm] using Metric.mem_ball.mp hq.1.1
  have htri := dist_triangle p (0 : Plane) q
  constructor
  · linarith only [hp₀, hq₀, ht, habs, hcoord]
  · linarith only [hpR, hqR, htri, hR]

/-- The geometric construction avoids positive integer distances for any
center choice; empty or degenerate choices are harmless. -/
theorem lobes_no_positive_integer_distances (R c t : ℝ) (m : ℕ)
    (hR : 2 * R ≤ (m : ℝ)) (ht : 2 * t = (m : ℝ) - 1) :
    ∀ p ∈ lobes R c t, ∀ q ∈ lobes R c t,
      p ≠ q → ∀ n : ℕ, 0 < n → dist p q ≠ (n : ℝ) := by
  intro p hp q hq hpq n hn heq
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcross : ∀ p ∈ rightLobe R c t, ∀ q ∈ leftLobe R c t,
      dist p q ≠ (n : ℝ) := by
    intro x hx y hy hxy
    obtain ⟨hlo, hhi⟩ := cross_lobe_distance_between R c t m hR ht hx hy
    by_cases hnm : n < m
    · have hle : n + 1 ≤ m := by omega
      have hleR : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hle
      linarith only [hlo, hxy, hleR]
    · have hle : m ≤ n := by omega
      have hleR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
      linarith only [hhi, hxy, hleR]
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · have hsmall := rightLobe_dist_lt_one hp hq
    linarith only [hsmall, hnR, heq]
  · exact hcross p hp q hq heq
  · exact hcross q hq p hp (by simpa only [dist_comm] using heq)
  · have hsmall := leftLobe_dist_lt_one hp hq
    linarith only [hsmall, hnR, heq]

/-- The same construction is admissible throughout each radius interval. -/
theorem lobes_admissible (R c t : ℝ) (m : ℕ)
    (hR : 2 * R ≤ (m : ℝ)) (ht : 2 * t = (m : ℝ) - 1) :
    AdmissibleOpenSet R (lobes R c t) := by
  refine ⟨(lobes_isOpen _ _ _).measurableSet, ?_, ?_⟩
  · intro p hp
    rcases hp with hp | hp <;> exact hp.1.1
  · exact lobes_no_positive_integer_distances _ _ _ m hR ht

/-- A concrete admissible open set at every half-integer radius `m/2`. -/
theorem half_integer_lobes_admissible (m : ℕ) (c : ℝ) :
    AdmissibleOpenSet ((m : ℝ) / 2)
      (lobes ((m : ℝ) / 2) c (((m : ℝ) - 1) / 2)) :=
  lobes_admissible _ _ _ m (by linarith) (by ring)

/-- The exact area, once evaluated, is automatically a lower bound for the
standalone extremal quantity. No area formula is assumed in this theorem. -/
theorem half_integer_lobes_area_le_Mopen (m : ℕ) (c : ℝ) :
    area (lobes ((m : ℝ) / 2) c (((m : ℝ) - 1) / 2)) ≤ Mopen ((m : ℝ) / 2) :=
  area_le_Mopen_of_admissible (half_integer_lobes_admissible m c)

#print axioms cross_lobe_distance_between
#print axioms lobes_no_positive_integer_distances
#print axioms lobes_admissible
#print axioms half_integer_lobes_admissible
#print axioms half_integer_lobes_area_le_Mopen

end
end Erdos953Lower.SmallRadiusLobes
