/-
  Erdős Problem 953: turn the quantitative digit bounds into a fixed
  distance gap from the integer lattice.
-/
import Erdos953Lower.DistanceGap

namespace Erdos953Lower

noncomputable section

set_option maxHeartbeats 20000

/-- A generic algebraic bridge for the planar digit construction.
`X` is the leading linear place, `D` its digit magnitude, `b` the
horizontal coordinate difference, and `a` the integral vertical
coordinate difference. -/
theorem distance_gap_of_digit_bounds (k : ℕ) (hk : 3 ≤ k)
    (D X : ℝ) (a b : ℤ)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ (k : ℝ) - 2)
    (hX : 1 ≤ X)
    (hb₁ : D * X ≤ (k : ℝ) * (b : ℝ))
    (hb₂ : (b : ℝ) ≤ 2 * D * X)
    (ha₁ : 4 * (k : ℝ) ^ 2 * D * X ^ 2 ≤ (a : ℝ))
    (ha₂ : (a : ℝ) ≤ 16 * (k : ℝ) ^ 2 * D * X ^ 2) :
    1 / (48 * (k : ℝ) ^ 4) <
      distToInt (Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)) := by
  let K : ℝ := k
  let B : ℝ := b
  let A : ℝ := a
  let δ : ℝ := 1 / (48 * K ^ 4)
  have hK : 3 ≤ K := by
    change (3 : ℝ) ≤ (k : ℝ)
    exact_mod_cast hk
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hX0 : 0 ≤ X := by linarith only [hX]
  have hD0 : 0 ≤ D := by linarith only [hD₁]
  have hB0 : 0 ≤ B := by
    by_contra hneg
    have hKBneg : K * B < 0 :=
      mul_neg_of_pos_of_neg (by linarith only [hK]) (lt_of_not_ge hneg)
    have hDXnonneg : 0 ≤ D * X := mul_nonneg hD0 hX0
    linarith only [hb₁, hKBneg, hDXnonneg]
  have hKB0 : 0 ≤ K * B := mul_nonneg hK0 hB0
  have hBX : 0 ≤ 2 * D * X - B := by
    dsimp [B] at hb₂ ⊢
    linarith only [hb₂]
  have hXle : X ≤ K * B := by
    have hmul : 0 ≤ (D - 1) * X :=
      mul_nonneg (by linarith only [hD₁]) hX0
    have hDX : X ≤ D * X := by nlinarith only [hmul]
    exact hDX.trans hb₁
  have hBsquare : B ^ 2 ≤ 4 * D ^ 2 * X ^ 2 := by
    nlinarith only [mul_nonneg hBX (show 0 ≤ 2 * D * X + B by positivity)]
  have hDleK : D ≤ K := by dsimp [K] at hD₂ ⊢; linarith only [hD₂]
  have hDleKsq : D ≤ K ^ 2 := by nlinarith only [hDleK, hK]
  have hDsquare : D ^ 2 ≤ K ^ 2 * D := by
    nlinarith only [mul_nonneg hD0
      (show 0 ≤ K ^ 2 - D by linarith only [hDleKsq])]
  have hUpperSq : B ^ 2 ≤ A := by
    have hmul := mul_le_mul_of_nonneg_left hDsquare
      (show 0 ≤ 4 * X ^ 2 by positivity)
    dsimp [A, K] at ha₁ ⊢
    nlinarith only [hBsquare, hmul, ha₁]
  have hLowerSq : A ≤ 16 * K ^ 4 * B ^ 2 := by
    have hDXsq : D * X ^ 2 ≤ K ^ 2 * B ^ 2 := by
      calc
        D * X ^ 2 = (D * X) * X := by ring
        _ ≤ (K * B) * X := mul_le_mul_of_nonneg_right hb₁ hX0
        _ ≤ (K * B) * (K * B) := mul_le_mul_of_nonneg_left hXle hKB0
        _ = K ^ 2 * B ^ 2 := by ring
    calc
      A ≤ 16 * K ^ 2 * D * X ^ 2 := ha₂
      _ = (16 * K ^ 2) * (D * X ^ 2) := by ring
      _ ≤ (16 * K ^ 2) * (K ^ 2 * B ^ 2) :=
        mul_le_mul_of_nonneg_left hDXsq (by positivity)
      _ = 16 * K ^ 4 * B ^ 2 := by ring
  have hAone : (1 : ℝ) ≤ A := by
    have hKsq : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ (by linarith only [hK])
    have hXsq : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ hX
    have hprod : (1 : ℝ) ≤ 4 * K ^ 2 * D * X ^ 2 := by
      calc
        (1 : ℝ) ≤ 4 * 1 ^ 2 * 1 * 1 ^ 2 := by norm_num
        _ ≤ 4 * K ^ 2 * D * X ^ 2 := by
          gcongr
          linarith only [hK]
    exact hprod.trans ha₁
  have ha : 1 ≤ a := by
    change (1 : ℝ) ≤ (a : ℝ) at hAone
    exact_mod_cast hAone
  have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ (by linarith only [hK])
  have hden : 0 < 48 * K ^ 4 := by positivity
  have hden' : 0 < 16 * K ^ 4 := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 1 / 4 := by
    dsimp [δ]
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)).2
    nlinarith only [hK4]
  have hlo : 3 * δ * (a : ℝ) ≤ (b : ℝ) ^ 2 := by
    have hquot : A / (16 * K ^ 4) ≤ B ^ 2 := by
      apply (div_le_iff₀ hden').2
      nlinarith only [hLowerSq]
    dsimp [δ, A, B] at *
    convert hquot using 1; ring
  have hhi : (b : ℝ) ^ 2 ≤ (a : ℝ) := by
    exact hUpperSq
  exact sqrt_sq_add_away a ((b : ℝ) ^ 2) δ ha hδ hδsmall hlo hhi

#print axioms distance_gap_of_digit_bounds

end

end Erdos953Lower
