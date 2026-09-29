import Erdos953Lower.Asymptotic
import Mathlib.Analysis.Real.Pi.Bounds

namespace Erdos953Lower

/-- A base of `k` cannot give an exponent exceeding one half. -/
theorem growthExponent_le_half (k : ℕ) (hk : 3 ≤ k) :
    growthExponent k ≤ (1 / 2 : ℝ) := by
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hdk : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by
    exact_mod_cast (by omega : k - 1 ≤ k)
  have hlog : Real.log ((k - 1 : ℕ) : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log hd hdk
  have hlogK : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by linarith)
  unfold growthExponent
  rw [Real.log_pow]
  exact (div_le_iff₀ (by linarith : 0 < 2 * Real.log (k : ℝ))).2 (by linarith)

/-- The disk-thickening coefficient loses at most twelve powers of the
digit base, with a uniform numerical constant. -/
theorem base_coefficient_ge_inv_pow (k : ℕ) (hk : 3 ≤ k) :
    (1 : ℝ) / (100000 * (k : ℝ) ^ 12) ≤
      (diskRadius k) ^ 2 * Real.pi /
        ((16 * (k : ℝ) ^ 2 + 1) ^ growthExponent k *
          ((k - 1 : ℕ) : ℝ)) := by
  let K : ℝ := k
  let d : ℝ := ((k - 1 : ℕ) : ℝ)
  let C : ℝ := 16 * K ^ 2 + 1
  let s : ℝ := growthExponent k
  let Q : ℝ := C ^ s * d
  have hK : (3 : ℝ) ≤ K := by
    change (3 : ℝ) ≤ (k : ℝ)
    exact_mod_cast hk
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (by omega : 0 < k - 1)
  have hdk : d ≤ K := by
    dsimp [d, K]
    exact_mod_cast (by omega : k - 1 ≤ k)
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg K]
  have hs : s ≤ (1 / 2 : ℝ) := growthExponent_le_half k hk
  have hC25 : C ≤ (5 * K) ^ 2 := by
    dsimp [C]
    nlinarith [sq_nonneg K]
  have hsqrt : Real.sqrt C ≤ 5 * K := by
    calc
      Real.sqrt C ≤ Real.sqrt ((5 * K) ^ 2) := Real.sqrt_le_sqrt hC25
      _ = 5 * K := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 5 * K)]
  have hCrpow : C ^ s ≤ 5 * K := by
    calc
      C ^ s ≤ C ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hC hs
      _ = Real.sqrt C := (Real.sqrt_eq_rpow C).symm
      _ ≤ 5 * K := hsqrt
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQbound : Q ≤ 5 * K ^ 2 := by
    calc
      Q = C ^ s * d := rfl
      _ ≤ (5 * K) * d := mul_le_mul_of_nonneg_right hCrpow hd.le
      _ ≤ (5 * K) * K :=
        mul_le_mul_of_nonneg_left hdk (by positivity)
      _ = 5 * K ^ 2 := by ring
  have hρ : diskRadius k = 1 / (192 * K ^ 5) := by
    dsimp [diskRadius, gap, K]
    ring
  have hnum : (diskRadius k) ^ 2 * Real.pi =
      Real.pi / (36864 * K ^ 10) := by
    rw [hρ]
    ring
  have hden1 : 0 < 100000 * K ^ 12 := by positivity
  have hden2 : 0 < 36864 * K ^ 10 * Q := by positivity
  have hineq : 36864 * K ^ 10 * Q ≤
      100000 * K ^ 12 * Real.pi := by
    calc
      36864 * K ^ 10 * Q ≤ 36864 * K ^ 10 * (5 * K ^ 2) :=
        mul_le_mul_of_nonneg_left hQbound (by positivity)
      _ = 184320 * K ^ 12 := by ring
      _ ≤ 300000 * K ^ 12 := by
        nlinarith [pow_nonneg (by linarith : 0 ≤ K) 12]
      _ ≤ 100000 * K ^ 12 * Real.pi := by
        have hπ : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
        nlinarith [mul_le_mul_of_nonneg_left hπ
          (by positivity : 0 ≤ 100000 * K ^ 12)]
  have hmain : (1 : ℝ) / (100000 * K ^ 12) ≤
      Real.pi / (36864 * K ^ 10 * Q) :=
    (div_le_div_iff₀ hden1 hden2).2 (by
      simpa only [one_mul, mul_comm, mul_left_comm, mul_assoc] using hineq)
  change (1 : ℝ) / (100000 * K ^ 12) ≤
    (diskRadius k) ^ 2 * Real.pi / Q
  rw [hnum]
  calc
    (1 : ℝ) / (100000 * K ^ 12) ≤
        Real.pi / (36864 * K ^ 10 * Q) := hmain
    _ = (Real.pi / (36864 * K ^ 10)) / Q := by ring

/-- A digit base large enough compared with `log R` yields a square-root
area lower bound with explicit polynomial loss in the base. -/
theorem digitDisks_lower_sqrt_div_pow_with_base (k : ℕ) (hk : 3 ≤ k)
    (R : ℝ) (hR : 16 * (k : ℝ) ^ 2 + 1 ≤ R)
    (hlog : Real.log R ≤ (((k - 1 : ℕ) : ℝ))) :
    ∃ A : Set Plane,
      MeasurableSet A ∧
      A ⊆ Metric.ball (0 : Plane) R ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ)) ∧
      ((1 : ℝ) / (100000 * (k : ℝ) ^ 12)) *
        (Real.exp (-1) * Real.sqrt R) ≤
          (MeasureTheory.volume A).toReal := by
  obtain ⟨A, hmeas, hsubset, hno, harea⟩ :=
    digitDisks_lower_sqrt_with_base k hk R hR hlog
  have hcoef := base_coefficient_ge_inv_pow k hk
  have hroot : 0 ≤ Real.exp (-1) * Real.sqrt R := by positivity
  refine ⟨A, hmeas, hsubset, hno, ?_⟩
  exact (mul_le_mul_of_nonneg_right hcoef hroot).trans harea

#print axioms base_coefficient_ge_inv_pow
#print axioms digitDisks_lower_sqrt_div_pow_with_base

end Erdos953Lower
