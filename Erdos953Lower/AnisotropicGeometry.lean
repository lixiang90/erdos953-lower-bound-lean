/-
  Research extension of the eighth-log-power lower bound for Erdős 953.
  Rectangular perturbations retain a fixed horizontal width while only
  the vertical width scales with the distance gap.
  This module does not yet assert a measurable-set or asymptotic bound.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace Erdos953Lower

noncomputable section

set_option maxHeartbeats 200000

/-- A thin rectangular perturbation stays strictly between two consecutive
integers whenever `a` is integral. The statement here is purely real algebra. -/
theorem anisotropic_sqrt_between (a b ε u v : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 16)
    (hlow : 16 * a * ε ≤ b ^ 2) (hhi : b ^ 2 ≤ a)
    (hu : |u| ≤ 1 / 4) (hv : |v| ≤ ε) :
    a + ε < Real.sqrt ((a + v) ^ 2 + (b + u) ^ 2) ∧
      Real.sqrt ((a + v) ^ 2 + (b + u) ^ 2) < a + 1 - ε := by
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have ha0 : 0 ≤ a - ε := by linarith
  have hav0 : 0 ≤ a + v := by linarith
  have hbu0 : 0 ≤ b + u := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hblo : (3 / 4 : ℝ) * b ≤ b + u := by linarith
  have hbhi : b + u ≤ (5 / 4 : ℝ) * b := by linarith
  have hsquarelo : (3 / 4 : ℝ) ^ 2 * b ^ 2 ≤ (b + u) ^ 2 := by
    nlinarith only [mul_nonneg (by linarith only [hblo] :
      0 ≤ b + u - (3 / 4 : ℝ) * b)
      (by linarith only [hbu0, hb0] : 0 ≤ b + u + (3 / 4 : ℝ) * b)]
  have hsquarehi : (b + u) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 * b ^ 2 := by
    nlinarith only [mul_nonneg (by linarith only [hbhi] :
      0 ≤ (5 / 4 : ℝ) * b - (b + u))
      (by linarith only [hbu0, hb0] : 0 ≤ (5 / 4 : ℝ) * b + (b + u))]
  have hasquarelo : (a - ε) ^ 2 ≤ (a + v) ^ 2 := by
    nlinarith only [mul_nonneg (by linarith only [hv'.1] :
      0 ≤ a + v - (a - ε))
      (by linarith only [hav0, ha0] : 0 ≤ a + v + (a - ε))]
  have hasquarehi : (a + v) ^ 2 ≤ (a + ε) ^ 2 := by
    nlinarith only [mul_nonneg (by linarith only [hv'.2] :
      0 ≤ a + ε - (a + v))
      (by linarith only [hav0, ha, hε] : 0 ≤ a + ε + (a + v))]
  have hb2 : 1 ≤ b ^ 2 := by nlinarith only [hb]
  have hbase : 0 ≤ (a + v) ^ 2 + (b + u) ^ 2 := by positivity
  have hs0 := Real.sqrt_nonneg ((a + v) ^ 2 + (b + u) ^ 2)
  have hs2 := Real.sq_sqrt hbase
  constructor
  · have hstrict : (a + ε) ^ 2 < (a + v) ^ 2 + (b + u) ^ 2 := by
      nlinarith only [hasquarelo, hsquarelo, hlow, hb2]
    have he : 0 ≤ a + ε := by linarith only [ha, hε]
    nlinarith only [hstrict, hs2, hs0, he]
  · have haε : a * ε ≤ a / 16 := by
      nlinarith only [mul_nonneg (by linarith only [ha] : 0 ≤ a)
        (by linarith only [hεsmall] : 0 ≤ 1 / 16 - ε)]
    have hstrict : (a + v) ^ 2 + (b + u) ^ 2 < (a + 1 - ε) ^ 2 := by
      nlinarith only [hasquarehi, hsquarehi, hhi, haε, ha, hεsmall]
    have he : 0 ≤ a + 1 - ε := by linarith only [ha, hεsmall]
    nlinarith only [hstrict, hs2, hs0, he]

/-- Integer vertical coordinates convert the preceding interval into a
uniform nearest-integer gap for every rectangular perturbation. -/
theorem anisotropic_distance_gap (a : ℤ) (b ε u v : ℝ)
    (ha : (1 : ℝ) ≤ (a : ℝ)) (hb : 1 ≤ b)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 16)
    (hlow : 16 * (a : ℝ) * ε ≤ b ^ 2) (hhi : b ^ 2 ≤ (a : ℝ))
    (hu : |u| ≤ 1 / 4) (hv : |v| ≤ ε) :
    ∀ z : ℤ, ε < |Real.sqrt (((a : ℝ) + v) ^ 2 + (b + u) ^ 2) - (z : ℝ)| := by
  obtain ⟨hleft, hright⟩ := anisotropic_sqrt_between (a : ℝ) b ε u v
    ha hb hε hεsmall hlow hhi hu hv
  intro z
  have hz : z ≤ a ∨ a + 1 ≤ z := by omega
  rcases hz with hza | haz
  · have hza' : (z : ℝ) ≤ (a : ℝ) := by exact_mod_cast hza
    calc
      ε < Real.sqrt (((a : ℝ) + v) ^ 2 + (b + u) ^ 2) - (z : ℝ) := by
        linarith only [hleft, hza']
      _ ≤ |Real.sqrt (((a : ℝ) + v) ^ 2 + (b + u) ^ 2) - (z : ℝ)| := le_abs_self _
  · have haz' : (a : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast haz
    calc
      ε < -(Real.sqrt (((a : ℝ) + v) ^ 2 + (b + u) ^ 2) - (z : ℝ)) := by
        linarith only [hright, haz']
      _ ≤ |Real.sqrt (((a : ℝ) + v) ^ 2 + (b + u) ^ 2) - (z : ℝ)| := neg_le_abs _

#print axioms anisotropic_sqrt_between
#print axioms anisotropic_distance_gap

end

end Erdos953Lower
