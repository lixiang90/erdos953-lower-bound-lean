/- Coordinate estimates needed for rectangular thickening of the existing
Sárközy digit construction. The base and vertical scaling are unchanged. -/
import Erdos953Lower.FiniteGap
import Erdos953Lower.DigitPoints
import Erdos953Lower.AnisotropicGeometry

namespace Erdos953Lower

open Finset
noncomputable section
set_option maxHeartbeats 50000

/-- Expose the two square-ratio estimates used inside the old gap proof. -/
theorem digit_coordinate_ratio_bounds (k : ℕ) (hk : 3 ≤ k)
    (D X : ℝ) (a b : ℤ)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ (k : ℝ) - 2) (hX : 1 ≤ X)
    (hb₁ : D * X ≤ (k : ℝ) * (b : ℝ))
    (hb₂ : (b : ℝ) ≤ 2 * D * X)
    (ha₁ : 4 * (k : ℝ) * D * X ^ 2 ≤ (a : ℝ))
    (ha₂ : (a : ℝ) ≤ 16 * (k : ℝ) * D * X ^ 2) :
    1 ≤ a ∧ 1 ≤ b ∧ (b : ℝ) ^ 2 ≤ (a : ℝ) ∧
      (a : ℝ) ≤ 16 * (k : ℝ) ^ 3 * (b : ℝ) ^ 2 := by
  let K : ℝ := k
  let B : ℝ := b
  let A : ℝ := a
  have hK : 3 ≤ K := by dsimp [K]; exact_mod_cast hk
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hX0 : 0 ≤ X := by linarith only [hX]
  have hD0 : 0 ≤ D := by linarith only [hD₁]
  have hDXone : 1 ≤ D * X := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ D * X := by gcongr
  have hBpos : 0 < B := by
    by_contra hneg
    have hKB : K * B ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hK0 (le_of_not_gt hneg)
    linarith only [hb₁, hDXone, hKB]
  have hB0 : 0 ≤ B := hBpos.le
  have hbpos : 0 < b := by change 0 < (b : ℝ) at hBpos; exact_mod_cast hBpos
  have hb : 1 ≤ b := by omega
  have hKB0 : 0 ≤ K * B := mul_nonneg hK0 hB0
  have hBX : 0 ≤ 2 * D * X - B := by linarith only [hb₂]
  have hXle : X ≤ K * B := by
    have hmul : 0 ≤ (D - 1) * X :=
      mul_nonneg (by linarith only [hD₁]) hX0
    have hDX : X ≤ D * X := by nlinarith only [hmul]
    exact hDX.trans hb₁
  have hBsquare : B ^ 2 ≤ 4 * D ^ 2 * X ^ 2 := by
    nlinarith only [mul_nonneg hBX (show 0 ≤ 2 * D * X + B by positivity)]
  have hDleK : D ≤ K := by linarith only [hD₂]
  have hDsquare : D ^ 2 ≤ K * D := by
    nlinarith only [mul_nonneg hD0 (by linarith only [hDleK] : 0 ≤ K - D)]
  have hUpperSq : B ^ 2 ≤ A := by
    have hmul := mul_le_mul_of_nonneg_left hDsquare
      (show 0 ≤ 4 * X ^ 2 by positivity)
    nlinarith only [hBsquare, hmul, ha₁]
  have hLowerSq : A ≤ 16 * K ^ 3 * B ^ 2 := by
    have hDXsq : D * X ^ 2 ≤ K ^ 2 * B ^ 2 := by
      calc
        D * X ^ 2 = (D * X) * X := by ring
        _ ≤ (K * B) * X := mul_le_mul_of_nonneg_right hb₁ hX0
        _ ≤ (K * B) * (K * B) := mul_le_mul_of_nonneg_left hXle hKB0
        _ = K ^ 2 * B ^ 2 := by ring
    calc
      A ≤ 16 * K * D * X ^ 2 := ha₂
      _ = (16 * K) * (D * X ^ 2) := by ring
      _ ≤ (16 * K) * (K ^ 2 * B ^ 2) :=
        mul_le_mul_of_nonneg_left hDXsq (by positivity)
      _ = 16 * K ^ 3 * B ^ 2 := by ring
  have hAone : (1 : ℝ) ≤ A := by
    have hprod : (1 : ℝ) ≤ 4 * K * D * X ^ 2 := by
      calc
        (1 : ℝ) ≤ 4 * 1 * 1 * 1 ^ 2 := by norm_num
        _ ≤ 4 * K * D * X ^ 2 := by
          gcongr
          linarith only [hK]
    exact hprod.trans ha₁
  have ha : 1 ≤ a := by change (1 : ℝ) ≤ (a : ℝ) at hAone; exact_mod_cast hAone
  exact ⟨ha, hb, hUpperSq, hLowerSq⟩

/-- The existing signed digit differences satisfy the rectangular hypotheses. -/
theorem finite_digit_coordinate_ratios (k i : ℕ) (d : ℕ → ℤ)
    (hk : 3 ≤ k) (hbound : ∀ j ≤ i, |d j| ≤ (k : ℤ) - 2)
    (hdi : d i ≠ 0) :
    let A : ℤ := 8 * (k : ℤ) *
      |∑ j ∈ range (i + 1), d j * (((k : ℤ) ^ 2) ^ j)|
    let B : ℤ := |∑ j ∈ range (i + 1), d j * (k : ℤ) ^ j|
    1 ≤ A ∧ 1 ≤ B ∧ (B : ℝ) ^ 2 ≤ (A : ℝ) ∧
      (A : ℝ) ≤ 16 * (k : ℝ) ^ 3 * (B : ℝ) ^ 2 := by
  let K : ℤ := k
  let L : ℤ := ∑ j ∈ range (i + 1), d j * K ^ j
  let Q : ℤ := ∑ j ∈ range (i + 1), d j * ((K ^ 2) ^ j)
  let A : ℤ := 8 * K * |Q|
  let B : ℤ := |L|
  let D : ℝ := (|d i| : ℤ)
  let X : ℝ := (k : ℝ) ^ i
  have hlow : ∀ j < i, |d j| ≤ K - 2 := by
    intro j hj
    exact hbound j (Nat.le_of_lt hj)
  have hlin := leading_linear_bounds k i d hk hlow hdi
  have hlinWeighted := leading_linear_weighted_lower k i d hk hlow hdi
  have hquad := leading_quadratic_bounds k i d hk hlow hdi
  have hD₁ : 1 ≤ D := by
    dsimp [D]
    have h : (1 : ℤ) ≤ |d i| := by
      have : 0 < |d i| := abs_pos.mpr hdi
      omega
    exact_mod_cast h
  have hD₂ : D ≤ (k : ℝ) - 2 := by dsimp [D]; exact_mod_cast hbound i le_rfl
  have hX : 1 ≤ X := by
    dsimp [X]
    apply one_le_pow₀
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith only [this]
  have hb₁ : D * X ≤ (k : ℝ) * (B : ℝ) := by
    dsimp [D, X, B, L, K] at hlinWeighted ⊢
    exact_mod_cast hlinWeighted
  have hb₂ : (B : ℝ) ≤ 2 * D * X := by
    dsimp [D, X, B, L, K] at hlin ⊢
    exact_mod_cast hlin.2
  have hpow : ((K ^ 2) ^ i) = (K ^ i) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hquad₁ : |d i| * (K ^ i) ^ 2 ≤ 2 * |Q| := by
    simpa [Q, K, hpow] using hquad.1
  have hquad₂ : |Q| ≤ 2 * |d i| * (K ^ i) ^ 2 := by
    simpa [Q, K, hpow] using hquad.2
  have hA₁_int : 4 * K * |d i| * (K ^ i) ^ 2 ≤ A := by
    have hscale : 0 ≤ 4 * K * (2 * |Q| - |d i| * (K ^ i) ^ 2) :=
      mul_nonneg (by positivity) (by linarith only [hquad₁])
    dsimp [A]
    nlinarith only [hscale]
  have hA₂_int : A ≤ 16 * K * |d i| * (K ^ i) ^ 2 := by
    have hscale : 0 ≤ 8 * K * (2 * |d i| * (K ^ i) ^ 2 - |Q|) :=
      mul_nonneg (by positivity) (by linarith only [hquad₂])
    dsimp [A]
    nlinarith only [hscale]
  have ha₁ : 4 * (k : ℝ) * D * X ^ 2 ≤ (A : ℝ) := by
    dsimp [D, X, K] at hA₁_int ⊢
    exact_mod_cast hA₁_int
  have ha₂ : (A : ℝ) ≤ 16 * (k : ℝ) * D * X ^ 2 := by
    dsimp [D, X, K] at hA₂_int ⊢
    exact_mod_cast hA₂_int
  exact digit_coordinate_ratio_bounds k hk D X A B hD₁ hD₂ hX hb₁ hb₂ ha₁ ha₂

/-- Every signed-digit difference has an integer gap after any perturbation
whose horizontal size is at most `1/4` and vertical size at most `1/(256k³)`. -/
theorem finite_digit_rectangular_gap (k i : ℕ) (d : ℕ → ℤ)
    (hk : 3 ≤ k) (hbound : ∀ j ≤ i, |d j| ≤ (k : ℤ) - 2)
    (hdi : d i ≠ 0) (u v : ℝ)
    (hu : |u| ≤ 1 / 4) (hv : |v| ≤ 1 / (256 * (k : ℝ) ^ 3)) :
    let A : ℤ := 8 * (k : ℤ) *
      |∑ j ∈ range (i + 1), d j * (((k : ℤ) ^ 2) ^ j)|
    let B : ℤ := |∑ j ∈ range (i + 1), d j * (k : ℤ) ^ j|
    ∀ z : ℤ, 1 / (256 * (k : ℝ) ^ 3) <
      |Real.sqrt (((A : ℝ) + v) ^ 2 + ((B : ℝ) + u) ^ 2) - (z : ℝ)| := by
  let A : ℤ := 8 * (k : ℤ) *
    |∑ j ∈ range (i + 1), d j * (((k : ℤ) ^ 2) ^ j)|
  let B : ℤ := |∑ j ∈ range (i + 1), d j * (k : ℤ) ^ j|
  have hrat := finite_digit_coordinate_ratios k i d hk hbound hdi
  change 1 ≤ A ∧ 1 ≤ B ∧ (B : ℝ) ^ 2 ≤ (A : ℝ) ∧
    (A : ℝ) ≤ 16 * (k : ℝ) ^ 3 * (B : ℝ) ^ 2 at hrat
  have hK : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hK0 : (0 : ℝ) < (k : ℝ) := by linarith only [hK]
  have hK3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ (by linarith only [hK])
  have hden : (0 : ℝ) < 256 * (k : ℝ) ^ 3 := by positivity
  have hε : (0 : ℝ) < 1 / (256 * (k : ℝ) ^ 3) := by positivity
  have hεsmall : (1 : ℝ) / (256 * (k : ℝ) ^ 3) ≤ 1 / 16 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 16)).2
    nlinarith only [hK3]
  have hquot : (A : ℝ) / (16 * (k : ℝ) ^ 3) ≤ (B : ℝ) ^ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (k : ℝ) ^ 3)).2
    nlinarith only [hrat.2.2.2]
  have hlow : 16 * (A : ℝ) * (1 / (256 * (k : ℝ) ^ 3)) ≤ (B : ℝ) ^ 2 := by
    convert hquot using 1
    ring
  exact anisotropic_distance_gap A (B : ℝ) (1 / (256 * (k : ℝ) ^ 3)) u v
    (by exact_mod_cast hrat.1) (by exact_mod_cast hrat.2.1)
    hε hεsmall hlow hrat.2.2.1 hu hv

/-- The actual coordinate differences of any two distinct centers satisfy
the same positive-integer square ratios. In particular their x coordinates
are distinct, which will make the thin rectangles disjoint. -/
theorem digitPoint_coordinate_ratios (k n : ℕ) (hk : 3 ≤ k)
    (α β : Fin n → Fin (k - 1)) (hab : α ≠ β) :
    let A : ℤ := |yCoord k n α - yCoord k n β|
    let B : ℤ := |xCoord k n α - xCoord k n β|
    1 ≤ A ∧ 1 ≤ B ∧ (B : ℝ) ^ 2 ≤ (A : ℝ) ∧
      (A : ℝ) ≤ 16 * (k : ℝ) ^ 3 * (B : ℝ) ^ 2 := by
  obtain ⟨i, hi, hdi, hzero, hbound⟩ :=
    exists_highest_digit_difference k n hk α β hab
  let d : ℕ → ℤ := digitDiff k n α β
  let L : ℤ := ∑ j ∈ range (i + 1), d j * (k : ℤ) ^ j
  let Q : ℤ := ∑ j ∈ range (i + 1), d j * (((k : ℤ) ^ 2) ^ j)
  have hx : xCoord k n α - xCoord k n β = L := by
    rw [xCoord_sub]
    exact digitDiff_sum_truncate k n i α β hi hzero (k : ℤ)
  have hy : yCoord k n α - yCoord k n β = 8 * (k : ℤ) * Q := by
    rw [yCoord_sub, digitDiff_sum_truncate k n i α β hi hzero]
  have hscale : (0 : ℤ) ≤ 8 * (k : ℤ) := by positivity
  have hrat := finite_digit_coordinate_ratios k i d hk hbound hdi
  dsimp only
  rw [hx, hy, abs_mul, abs_of_nonneg hscale]
  exact hrat

#print axioms digit_coordinate_ratio_bounds
#print axioms finite_digit_coordinate_ratios
#print axioms finite_digit_rectangular_gap
#print axioms digitPoint_coordinate_ratios

end
end Erdos953Lower
