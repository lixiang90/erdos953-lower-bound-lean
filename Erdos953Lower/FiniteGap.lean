/-
  Erdős Problem 953: combine the leading-digit bounds with the
  Euclidean distance-gap lemma.
-/
import Erdos953Lower.LeadingDigit
import Erdos953Lower.GeometryGap

namespace Erdos953Lower

open Finset

noncomputable section

/-- Any nonzero leading digit with lower digits bounded in magnitude
produces a pairwise distance uniformly separated from the integers.
The corresponding planar point difference has vertical coordinate
`8 k² |∑ dⱼ (k²)^j|` and horizontal coordinate `|∑ dⱼ k^j|`.
-/
theorem finite_digit_distance_gap (k i : ℕ) (d : ℕ → ℤ)
    (hk : 3 ≤ k)
    (hbound : ∀ j ≤ i, |d j| ≤ (k : ℤ) - 2)
    (hdi : d i ≠ 0) :
    1 / (48 * (k : ℝ) ^ 5) <
      distToInt (Real.sqrt (
        ((8 * (k : ℤ) ^ 2 *
          |∑ j ∈ range (i + 1), d j * (((k : ℤ) ^ 2) ^ j)| : ℤ) : ℝ) ^ 2 +
        ((|∑ j ∈ range (i + 1), d j * (k : ℤ) ^ j| : ℤ) : ℝ) ^ 2)) := by
  let K : ℤ := k
  let L : ℤ := ∑ j ∈ range (i + 1), d j * K ^ j
  let Q : ℤ := ∑ j ∈ range (i + 1), d j * ((K ^ 2) ^ j)
  let A : ℤ := 8 * K ^ 2 * |Q|
  let B : ℤ := |L|
  let D : ℝ := (|d i| : ℤ)
  let X : ℝ := (k : ℝ) ^ i
  have hlow : ∀ j < i, |d j| ≤ K - 2 := by
    intro j hj
    exact hbound j (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hj))
  have hlin := leading_linear_bounds k i d hk hlow hdi
  have hquad := leading_quadratic_bounds k i d hk hlow hdi
  have hD₁ : 1 ≤ D := by
    dsimp [D]
    have h : (1 : ℤ) ≤ |d i| := by
      have : 0 < |d i| := abs_pos.mpr hdi
      omega
    exact_mod_cast h
  have hD₂ : D ≤ (k : ℝ) - 2 := by
    dsimp [D]
    exact_mod_cast hbound i (Nat.le_refl i)
  have hX : 1 ≤ X := by
    dsimp [X]
    apply one_le_pow₀
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hb₁ : X ≤ (k : ℝ) * (B : ℝ) := by
    dsimp [X, B, L, K] at *
    exact_mod_cast hlin.1
  have hb₂ : (B : ℝ) ≤ 2 * D * X := by
    dsimp [D, X, B, L, K] at *
    exact_mod_cast hlin.2
  have hpow : ((K ^ 2) ^ i) = (K ^ i) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hKsq : 0 ≤ K ^ 2 := sq_nonneg K
  have hquad₁ : |d i| * (K ^ i) ^ 2 ≤ 2 * |Q| := by
    simpa [Q, K, hpow] using hquad.1
  have hquad₂ : |Q| ≤ 2 * |d i| * (K ^ i) ^ 2 := by
    simpa [Q, K, hpow] using hquad.2
  have hA₁_int : 4 * K ^ 2 * |d i| * (K ^ i) ^ 2 ≤ A := by
    have hscale : 0 ≤ 4 * K ^ 2 * (2 * |Q| - |d i| * (K ^ i) ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    dsimp [A]
    nlinarith
  have hA₂_int : A ≤ 16 * K ^ 2 * |d i| * (K ^ i) ^ 2 := by
    have hscale : 0 ≤ 8 * K ^ 2 *
        (2 * |d i| * (K ^ i) ^ 2 - |Q|) :=
      mul_nonneg (by positivity) (by linarith)
    dsimp [A]
    nlinarith
  have ha₁ : 4 * (k : ℝ) ^ 2 * D * X ^ 2 ≤ (A : ℝ) := by
    dsimp [D, X, K] at *
    exact_mod_cast hA₁_int
  have ha₂ : (A : ℝ) ≤ 16 * (k : ℝ) ^ 2 * D * X ^ 2 := by
    dsimp [D, X, K] at *
    exact_mod_cast hA₂_int
  have hgap := distance_gap_of_digit_bounds k hk D X A B
    hD₁ hD₂ hX hb₁ hb₂ ha₁ ha₂
  simpa [A, B, L, Q, K] using hgap

#print axioms finite_digit_distance_gap

end

end Erdos953Lower
