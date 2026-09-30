import Erdos953Lower.Coefficient

namespace Erdos953Lower

/-- A concrete threshold ensuring that a digit base near `log R` has
geometric scale small enough to fit inside the radius-`R` disk. -/
theorem log_square_radius_bound (R : ℝ) (hR : (1000 : ℝ) ^ 4 ≤ R) :
    16 * (Real.log R + 3) ^ 2 + 1 ≤ R := by
  let t : ℝ := R ^ (1 / 4 : ℝ)
  have hRpos : 0 < R := by nlinarith
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht4 : t ^ 4 = R := by
    dsimp [t]
    rw [← Real.rpow_natCast (R ^ (1 / 4 : ℝ)) 4]
    rw [← Real.rpow_mul hRpos.le]
    norm_num
  have ht1000 : (1000 : ℝ) ≤ t := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (1000 : ℝ) ^ 4)
      hR (by norm_num : 0 ≤ (1 / 4 : ℝ))
    have hconst : ((1000 : ℝ) ^ 4) ^ (1 / 4 : ℝ) = 1000 := by
      rw [← Real.rpow_natCast (1000 : ℝ) 4]
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (1000 : ℝ))]
      norm_num
    simpa only [t, hconst] using h
  have hlog : Real.log R ≤ 4 * t := by
    have h := Real.log_le_rpow_div hRpos.le (by norm_num : 0 < (1 / 4 : ℝ))
    calc
      Real.log R ≤ R ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := h
      _ = 4 * t := by dsimp [t]; ring
  have hlog3 : Real.log R + 3 ≤ 5 * t := by linarith
  have hlog0 : 0 ≤ Real.log R + 3 := by
    have hlog0 : 0 ≤ Real.log R := Real.log_nonneg (by nlinarith)
    linarith
  have hsq : (Real.log R + 3) ^ 2 ≤ (5 * t) ^ 2 :=
    (sq_le_sq₀ hlog0 (by positivity)).2 hlog3
  have ht2 : (1000000 : ℝ) ≤ t ^ 2 := by nlinarith
  have hmain : 400 * t ^ 2 + 1 ≤ t ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)]
  calc
    16 * (Real.log R + 3) ^ 2 + 1 ≤ 400 * t ^ 2 + 1 := by
      nlinarith [hsq]
    _ ≤ t ^ 4 := hmain
    _ = R := ht4

/-- The ceiling of `log R`, plus two, meets both the scale constraint and
the exponent constraint for every sufficiently large `R`. -/
theorem choose_digit_base (R : ℝ) (hR : (1000 : ℝ) ^ 4 ≤ R) :
    ∃ k : ℕ, 3 ≤ k ∧
      Real.log R ≤ (((k - 1 : ℕ) : ℝ)) ∧
      16 * (k : ℝ) ^ 2 + 1 ≤ R ∧
      (k : ℝ) ≤ Real.log R + 3 := by
  let n : ℕ := Nat.ceil (Real.log R)
  let k : ℕ := n + 2
  have hRone : 1 < R := by nlinarith
  have hlog0 : 0 ≤ Real.log R := (Real.log_pos hRone).le
  have hceilLow : Real.log R ≤ (n : ℝ) := Nat.le_ceil _
  have hceilUp : (n : ℝ) < Real.log R + 1 := Nat.ceil_lt_add_one hlog0
  have hn : 0 < n := by
    by_contra hnot
    have hn0 : n = 0 := by omega
    rw [hn0] at hceilLow
    norm_num at hceilLow
    linarith [Real.log_pos hRone]
  have hk : 3 ≤ k := by dsimp [k]; omega
  have hlog : Real.log R ≤ (((k - 1 : ℕ) : ℝ)) := by
    have heq : k - 1 = n + 1 := by dsimp [k]
    rw [heq]
    push_cast
    linarith
  have hKbound : (k : ℝ) ≤ Real.log R + 3 := by
    dsimp [k]
    push_cast
    linarith
  have hsq : (k : ℝ) ^ 2 ≤ (Real.log R + 3) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) (by linarith)).2 hKbound
  have hfit : 16 * (k : ℝ) ^ 2 + 1 ≤ R := by
    nlinarith [log_square_radius_bound R hR]
  exact ⟨k, hk, hlog, hfit, hKbound⟩

/-- An unconditional, explicit near-square-root lower bound for every disk
radius above the stated numerical threshold. -/
theorem erdos953_lower_polylog (R : ℝ) (hR : (1000 : ℝ) ^ 4 ≤ R) :
    ∃ A : Set Erdos953Lower.Plane,
      MeasurableSet A ∧
      A ⊆ Metric.ball (0 : Erdos953Lower.Plane) R ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ)) ∧
      ((1 : ℝ) / (100000 * (Real.log R + 3) ^ 10)) *
        (Real.exp (-1) * Real.sqrt R) ≤
          (MeasureTheory.volume A).toReal := by
  obtain ⟨k, hk, hlog, hfit, hKbound⟩ := choose_digit_base R hR
  obtain ⟨A, hmeas, hsubset, hno, harea⟩ :=
    Erdos953Lower.digitDisks_lower_sqrt_div_pow_with_base
      k hk R hfit hlog
  have hLpos : 0 < Real.log R + 3 := by
    have hRone : 1 ≤ R := by nlinarith
    have := Real.log_nonneg hRone
    linarith
  have hKpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpow : (k : ℝ) ^ 10 ≤ (Real.log R + 3) ^ 10 :=
    pow_le_pow_left₀ hKpos.le hKbound 10
  have hdenK : 0 < 100000 * (k : ℝ) ^ 10 := by positivity
  have hdenL : 0 < 100000 * (Real.log R + 3) ^ 10 := by positivity
  have hcoef : (1 : ℝ) / (100000 * (Real.log R + 3) ^ 10) ≤
      1 / (100000 * (k : ℝ) ^ 10) :=
    (div_le_div_iff₀ hdenL hdenK).2 (by nlinarith [hpow])
  have hroot : 0 ≤ Real.exp (-1) * Real.sqrt R := by positivity
  refine ⟨A, hmeas, hsubset, hno, ?_⟩
  exact (mul_le_mul_of_nonneg_right hcoef hroot).trans harea

#print axioms erdos953_lower_polylog

end Erdos953Lower
