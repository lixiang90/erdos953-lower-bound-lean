/-
  Erdős Problem 953: turn the quantitative digit bounds into a fixed
  distance gap from the integer lattice.
-/
import Erdos953Lower.DistanceGap

namespace Erdos953Lower

noncomputable section

/-- A generic algebraic bridge for the planar digit construction.
`X` is the leading linear place, `D` its digit magnitude, `b` the
horizontal coordinate difference, and `a` the integral vertical
coordinate difference. -/
theorem distance_gap_of_digit_bounds (k : ℕ) (hk : 3 ≤ k)
    (D X : ℝ) (a b : ℤ)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ (k : ℝ) - 2)
    (hX : 1 ≤ X)
    (hb₁ : X ≤ (k : ℝ) * (b : ℝ))
    (hb₂ : (b : ℝ) ≤ 2 * D * X)
    (ha₁ : 4 * (k : ℝ) ^ 2 * D * X ^ 2 ≤ (a : ℝ))
    (ha₂ : (a : ℝ) ≤ 16 * (k : ℝ) ^ 2 * D * X ^ 2) :
    1 / (48 * (k : ℝ) ^ 5) <
      distToInt (Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)) := by
  let K : ℝ := k
  let B : ℝ := b
  let A : ℝ := a
  let δ : ℝ := 1 / (48 * K ^ 5)
  have hK : 3 ≤ K := by
    change (3 : ℝ) ≤ (k : ℝ)
    exact_mod_cast hk
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ B := by
    dsimp [B, K] at *
    nlinarith
  have hX0 : 0 ≤ X := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hKB0 : 0 ≤ K * B := mul_nonneg hK0 hB0
  have hBX : 0 ≤ 2 * D * X - B := by dsimp [B] at *; linarith
  have hXsquare : X ^ 2 ≤ K ^ 2 * B ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ K * B - X by dsimp [K, B] at *; linarith)
      (show 0 ≤ K * B + X by positivity)]
  have hBsquare : B ^ 2 ≤ 4 * D ^ 2 * X ^ 2 := by
    nlinarith [mul_nonneg hBX (show 0 ≤ 2 * D * X + B by positivity)]
  have hDleK : D ≤ K := by dsimp [K] at *; linarith
  have hDleKsq : D ≤ K ^ 2 := by nlinarith
  have hDsquare : D ^ 2 ≤ K ^ 2 * D := by
    nlinarith [mul_nonneg hD0 (show 0 ≤ K ^ 2 - D by linarith)]
  have hUpperSq : B ^ 2 ≤ A := by
    have hmul : 0 ≤ 4 * X ^ 2 * (K ^ 2 * D - D ^ 2) := by positivity
    dsimp [A, K] at *
    nlinarith
  have hLowerSq : A ≤ 16 * K ^ 5 * B ^ 2 := by
    have hmul₁ : 0 ≤ 16 * K ^ 2 * X ^ 2 * (K - D) := by positivity
    have hmul₂ : 0 ≤ 16 * K ^ 3 * (K ^ 2 * B ^ 2 - X ^ 2) := by positivity
    dsimp [A, K, B] at *
    nlinarith
  have hAone : (1 : ℝ) ≤ A := by
    dsimp [A, K] at *
    nlinarith [sq_nonneg (X - 1), sq_nonneg ((k : ℝ) - 3)]
  have ha : 1 ≤ a := by
    change (1 : ℝ) ≤ (a : ℝ) at hAone
    exact_mod_cast hAone
  have hK5 : 1 ≤ K ^ 5 := one_le_pow₀ (by linarith)
  have hden : 0 < 48 * K ^ 5 := by positivity
  have hden' : 0 < 16 * K ^ 5 := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 1 / 4 := by
    dsimp [δ]
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)).2
    nlinarith
  have hlo : 3 * δ * (a : ℝ) ≤ (b : ℝ) ^ 2 := by
    have hquot : A / (16 * K ^ 5) ≤ B ^ 2 := by
      apply (div_le_iff₀ hden').2
      nlinarith [hLowerSq]
    dsimp [δ, A, B] at *
    convert hquot using 1 <;> ring
  have hhi : (b : ℝ) ^ 2 ≤ (a : ℝ) := by
    exact hUpperSq
  exact sqrt_sq_add_away a ((b : ℝ) ^ 2) δ ha hδ hδsmall hlo hhi

#print axioms distance_gap_of_digit_bounds

end

end Erdos953Lower
