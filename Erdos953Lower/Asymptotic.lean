/-
  Radius selection for the lower-bound asymptotic.
-/
import Erdos953Lower.DigitDisks
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos953Lower

/-- Exponent produced by a fixed digit base. -/
noncomputable def growthExponent (k : ℕ) : ℝ :=
  Real.log ((k - 1 : ℕ) : ℝ) / Real.log ((k : ℝ) ^ 2)

theorem growthExponent_pos (k : ℕ) (hk : 3 ≤ k) : 0 < growthExponent k := by
  have hd : (1 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < k - 1)
  have hb : (1 : ℝ) < (k : ℝ) ^ 2 := by
    have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  unfold growthExponent
  exact div_pos (Real.log_pos hd) (Real.log_pos hb)

/-- Quantitative exponent loss from a digit base: it is at most the
reciprocal of the number of allowed digits. -/
theorem growthExponent_ge_half_sub_inv (k : ℕ) (hk : 3 ≤ k) :
    (1 / 2 : ℝ) - 1 / (((k - 1 : ℕ) : ℝ)) ≤ growthExponent k := by
  let K : ℝ := k
  let d : ℝ := ((k - 1 : ℕ) : ℝ)
  have hK : (3 : ℝ) ≤ K := by
    change (3 : ℝ) ≤ (k : ℝ)
    exact_mod_cast hk
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (by omega : 0 < k - 1)
  have hKd : K = d + 1 := by
    dsimp [K, d]
    exact_mod_cast (by omega : k = (k - 1) + 1)
  have hL : (1 / 2 : ℝ) ≤ Real.log K := by
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      linarith
    exact h2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hdiff : Real.log K - Real.log d ≤ 1 / d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < K / d by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h
    have hq : K / d - 1 = 1 / d := by
      rw [hKd]
      field_simp
      ring
    rw [hq] at h
    exact h
  have hden : Real.log (K ^ 2) = 2 * Real.log K := by
    rw [Real.log_pow]
    ring
  have hdiv : 1 / d ≤ (2 * Real.log K) / d :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hcore : (1 / 2 - 1 / d) * (2 * Real.log K) ≤ Real.log d := by
    calc
      (1 / 2 - 1 / d) * (2 * Real.log K) =
          Real.log K - (2 * Real.log K) / d := by ring
      _ ≤ Real.log K - 1 / d := by linarith
      _ ≤ Real.log d := by linarith
  unfold growthExponent
  change 1 / 2 - 1 / d ≤ Real.log d / Real.log (K ^ 2)
  rw [hden]
  exact (le_div_iff₀ (by linarith : 0 < 2 * Real.log K)).2 hcore

/-- If the number of allowed digits is at least `log R`, the finite-base
construction already reaches a fixed fraction of the square-root scale,
before accounting for the disk-thickening coefficient. -/
theorem exp_neg_one_mul_sqrt_le_rpow_growthExponent
    (k : ℕ) (hk : 3 ≤ k) (R : ℝ) (hR : 1 ≤ R)
    (hlog : Real.log R ≤ (((k - 1 : ℕ) : ℝ))) :
    Real.exp (-1) * Real.sqrt R ≤ R ^ growthExponent k := by
  let d : ℝ := ((k - 1 : ℕ) : ℝ)
  let s : ℝ := growthExponent k
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (by omega : 0 < k - 1)
  have hRpos : 0 < R := by linarith
  have hlog0 : 0 ≤ Real.log R := Real.log_nonneg hR
  have hs : 1 / 2 - 1 / d ≤ s := growthExponent_ge_half_sub_inv k hk
  have hdiv : Real.log R / d ≤ 1 :=
    (div_le_iff₀ hd).2 (by simpa [d] using hlog)
  have hmul := mul_le_mul_of_nonneg_right hs hlog0
  have hidentity : (1 / 2 - 1 / d) * Real.log R =
      (1 / 2) * Real.log R - Real.log R / d := by ring
  rw [hidentity] at hmul
  have he : (1 / 2) * Real.log R - 1 ≤ s * Real.log R := by linarith
  have hexp := Real.exp_le_exp.mpr he
  have hleft : Real.exp (-1) * Real.sqrt R =
      Real.exp ((1 / 2) * Real.log R - 1) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hRpos]
    rw [← Real.exp_add]
    congr 1
    ring
  have hright : R ^ growthExponent k = Real.exp (s * Real.log R) := by
    rw [Real.rpow_def_of_pos hRpos]
    congr 1
    ring
  rw [hleft, hright]
  exact hexp

theorem base_pow_growthExponent (k : ℕ) (hk : 3 ≤ k) :
    ((k : ℝ) ^ 2) ^ growthExponent k = ((k - 1 : ℕ) : ℝ) := by
  have hd : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hb : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have hlog : Real.log ((k : ℝ) ^ 2) ≠ 0 := by
    apply ne_of_gt (Real.log_pos ?_)
    have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  rw [Real.rpow_def_of_pos hb]
  unfold growthExponent
  have hcancel : Real.log ((k : ℝ) ^ 2) *
      (Real.log ((k - 1 : ℕ) : ℝ) / Real.log ((k : ℝ) ^ 2)) =
      Real.log ((k - 1 : ℕ) : ℝ) := by
    field_simp
  rw [hcancel, Real.exp_log hd]

theorem digitDisks_volume_real (k n : ℕ) (hk : 3 ≤ k) :
    (MeasureTheory.volume (digitDisks k n)).toReal =
      (((k - 1) ^ n : ℕ) : ℝ) * (diskRadius k) ^ 2 * Real.pi := by
  have hρ : 0 ≤ diskRadius k := by
    unfold diskRadius gap
    positivity
  rw [digitDisks_volume k n hk]
  have hnat : (((k - 1) ^ n : ℕ) : ENNReal).toReal =
      (((k - 1) ^ n : ℕ) : ℝ) := ENNReal.toReal_natCast _
  have hball : (ENNReal.ofReal (diskRadius k) ^ 2 * ENNReal.ofReal Real.pi).toReal =
      (diskRadius k) ^ 2 * Real.pi := by
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hρ, Real.pi_nonneg]
  rw [ENNReal.toReal_mul, hnat, hball]
  ring

/-- Every radius above one is between two consecutive powers of a fixed base. -/
theorem exists_nat_pow_le_lt (b R : ℝ) (hb : 1 < b) (hR : 1 ≤ R) :
    ∃ n : ℕ, b ^ n ≤ R ∧ R < b ^ (n + 1) := by
  classical
  let H : ∃ m : ℕ, R < b ^ m := pow_unbounded_of_one_lt R hb
  let m : ℕ := Nat.find H
  have hm : R < b ^ m := Nat.find_spec H
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hm
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hnlt : n < Nat.find H := by
    change n < m
    omega
  have hlow : b ^ n ≤ R := le_of_not_gt (Nat.find_min H hnlt)
  refine ⟨n, hlow, ?_⟩
  simpa [m, hn, Nat.succ_eq_add_one] using hm

/-- The actual disk radius is bounded by a constant times the geometric scale. -/
theorem digitDisks_radius_le_geometric (k n : ℕ) (hk : 3 ≤ k) :
    16 * (k : ℝ) ^ 2 * (((k : ℝ) ^ 2) ^ n) + diskRadius k ≤
      (16 * (k : ℝ) ^ 2 + 1) * (((k : ℝ) ^ 2) ^ n) := by
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hb : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hbn : (1 : ℝ) ≤ (((k : ℝ) ^ 2) ^ n) := one_le_pow₀ hb
  have hρ : diskRadius k < 1 := diskRadius_lt_one k hk
  nlinarith

/-- At every sufficiently large radius, one of the digit-disk sets fits,
and its scale is within one geometric step of that radius. -/
theorem digitDisks_at_any_large_radius (k : ℕ) (hk : 3 ≤ k)
    (R : ℝ) (hR : 16 * (k : ℝ) ^ 2 + 1 ≤ R) :
    ∃ n : ℕ, ∃ A : Set Plane,
      MeasurableSet A ∧
      A ⊆ Metric.ball (0 : Plane) R ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ)) ∧
      MeasureTheory.volume A = (((k - 1) ^ n : ℕ) : ENNReal) *
        (ENNReal.ofReal (diskRadius k) ^ 2 * ENNReal.ofReal Real.pi) ∧
      R < (16 * (k : ℝ) ^ 2 + 1) * (((k : ℝ) ^ 2) ^ (n + 1)) := by
  let C : ℝ := 16 * (k : ℝ) ^ 2 + 1
  let b : ℝ := (k : ℝ) ^ 2
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 1 < b := by dsimp [b]; nlinarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hT : 1 ≤ R / C := by
    apply (le_div_iff₀ hC).2
    simpa [C] using hR
  obtain ⟨n, hlow, hhigh⟩ := exists_nat_pow_le_lt b (R / C) hb hT
  have hCbn : C * b ^ n ≤ R := by
    have h := (le_div_iff₀ hC).1 hlow
    nlinarith
  have hRnext : R < C * b ^ (n + 1) := by
    have h := (div_lt_iff₀ hC).1 hhigh
    nlinarith
  refine ⟨n, digitDisks k n, digitDisks_measurable k n, ?_,
    digitDisks_no_positive_integer_distances k n hk,
    digitDisks_volume k n hk, ?_⟩
  · intro x hx
    have hxball := digitDisks_subset_ball k n hk hx
    have hxrad : dist x (0 : Plane) <
        16 * (k : ℝ) ^ 2 * (((k : ℝ) ^ 2) ^ n) + diskRadius k := by
      simpa [Metric.mem_ball, dist_comm] using hxball
    have hfit : 16 * (k : ℝ) ^ 2 * (((k : ℝ) ^ 2) ^ n) + diskRadius k ≤ R := by
      calc
        _ ≤ C * b ^ n := by simpa [C, b] using digitDisks_radius_le_geometric k n hk
        _ ≤ R := hCbn
    simpa [Metric.mem_ball, dist_comm] using (lt_of_lt_of_le hxrad hfit)
  · simpa [C, b] using hRnext

/-- A fixed digit base gives a power-law lower bound with an explicit
coefficient. This form permits the base to depend on the target radius. -/
theorem digitDisks_lower_growth_explicit (k : ℕ) (hk : 3 ≤ k) :
    ∀ R : ℝ, 16 * (k : ℝ) ^ 2 + 1 ≤ R →
      ∃ A : Set Plane,
        MeasurableSet A ∧
        A ⊆ Metric.ball (0 : Plane) R ∧
        (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
          ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ)) ∧
        ((diskRadius k) ^ 2 * Real.pi /
          ((16 * (k : ℝ) ^ 2 + 1) ^ growthExponent k *
            ((k - 1 : ℕ) : ℝ))) * R ^ growthExponent k ≤
          (MeasureTheory.volume A).toReal := by
  let C : ℝ := 16 * (k : ℝ) ^ 2 + 1
  let b : ℝ := (k : ℝ) ^ 2
  let d : ℝ := ((k - 1 : ℕ) : ℝ)
  let s : ℝ := growthExponent k
  let a : ℝ := (diskRadius k) ^ 2 * Real.pi
  let Q : ℝ := C ^ s * d
  have hK : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hC : 0 < C := by dsimp [C]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (by omega : 0 < k - 1)
  have hs : 0 < s := growthExponent_pos k hk
  have hρ : 0 < diskRadius k := by
    unfold diskRadius gap
    positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  intro R hR
  obtain ⟨n, A, hmeas, hsubset, hno, hvol, hRnext⟩ :=
    digitDisks_at_any_large_radius k hk R hR
  have hR0 : 0 ≤ R := by dsimp [C] at hC; linarith
  have hRpow : R ^ s ≤ Q * d ^ n := by
    have hmono := Real.rpow_le_rpow hR0 hRnext.le hs.le
    calc
      R ^ s ≤ (C * b ^ (n + 1)) ^ s := by simpa [C, b, s] using hmono
      _ = C ^ s * (b ^ s) ^ (n + 1) := by
        rw [Real.mul_rpow hC.le (pow_nonneg hb.le _), Real.rpow_pow_comm hb.le]
      _ = Q * d ^ n := by
        rw [show b ^ s = d from base_pow_growthExponent k hk]
        dsimp [Q]
        rw [pow_succ]
        ring
  have hvolreal : (MeasureTheory.volume A).toReal = a * d ^ n := by
    rw [hvol]
    have hnat : (((k - 1) ^ n : ℕ) : ENNReal).toReal =
        (((k - 1) ^ n : ℕ) : ℝ) := ENNReal.toReal_natCast _
    have hball : (ENNReal.ofReal (diskRadius k) ^ 2 * ENNReal.ofReal Real.pi).toReal = a := by
      dsimp [a]
      simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hρ.le, Real.pi_nonneg]
    rw [ENNReal.toReal_mul, hnat, hball]
    simp [d, a, mul_comm]
  refine ⟨A, hmeas, hsubset, hno, ?_⟩
  rw [hvolreal]
  change (a / Q) * R ^ s ≤ a * d ^ n
  have hc : 0 ≤ a / Q := (div_pos ha hQ).le
  calc
    (a / Q) * R ^ growthExponent k ≤ (a / Q) * (Q * d ^ n) := by
      exact mul_le_mul_of_nonneg_left (by simpa [s] using hRpow) hc
    _ = a * d ^ n := by
      field_simp [ne_of_gt hQ]

/-- A radius-dependent digit base with `k - 1 ≥ log R` gives an explicit
square-root lower bound whose remaining loss is entirely in its coefficient. -/
theorem digitDisks_lower_sqrt_with_base (k : ℕ) (hk : 3 ≤ k)
    (R : ℝ) (hR : 16 * (k : ℝ) ^ 2 + 1 ≤ R)
    (hlog : Real.log R ≤ (((k - 1 : ℕ) : ℝ))) :
    ∃ A : Set Plane,
      MeasurableSet A ∧
      A ⊆ Metric.ball (0 : Plane) R ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ)) ∧
      ((diskRadius k) ^ 2 * Real.pi /
        ((16 * (k : ℝ) ^ 2 + 1) ^ growthExponent k *
          ((k - 1 : ℕ) : ℝ))) *
        (Real.exp (-1) * Real.sqrt R) ≤
          (MeasureTheory.volume A).toReal := by
  obtain ⟨A, hmeas, hsubset, hno, harea⟩ :=
    digitDisks_lower_growth_explicit k hk R hR
  have hRone : 1 ≤ R := by
    have hK : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith [sq_nonneg (k : ℝ)]
  have hroot := exp_neg_one_mul_sqrt_le_rpow_growthExponent
    k hk R hRone hlog
  have hρ : 0 < diskRadius k := by
    unfold diskRadius gap
    positivity
  have hd : (0 : ℝ) < (((k - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hcoef : 0 ≤ (diskRadius k) ^ 2 * Real.pi /
      ((16 * (k : ℝ) ^ 2 + 1) ^ growthExponent k *
        ((k - 1 : ℕ) : ℝ)) := by positivity
  refine ⟨A, hmeas, hsubset, hno, ?_⟩
  exact (mul_le_mul_of_nonneg_left hroot hcoef).trans harea

/-- The existential-coefficient form used by the asymptotic theorem. -/
theorem digitDisks_lower_growth_fixed_base (k : ℕ) (hk : 3 ≤ k) :
    ∃ c : ℝ, 0 < c ∧
      ∀ R : ℝ, 16 * (k : ℝ) ^ 2 + 1 ≤ R →
        ∃ A : Set Plane,
          MeasurableSet A ∧
          A ⊆ Metric.ball (0 : Plane) R ∧
          (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
            ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ)) ∧
          c * R ^ growthExponent k ≤ (MeasureTheory.volume A).toReal := by
  let c : ℝ := (diskRadius k) ^ 2 * Real.pi /
    ((16 * (k : ℝ) ^ 2 + 1) ^ growthExponent k *
      ((k - 1 : ℕ) : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    have hk' : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    have hρ : 0 < diskRadius k := by
      unfold diskRadius gap
      positivity
    positivity
  exact ⟨c, hc, digitDisks_lower_growth_explicit k hk⟩

/-- The exponents from digit bases can be made arbitrarily close to one half. -/
theorem exists_growthExponent_gt_half_sub (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ 1 / 2 - ε < growthExponent k := by
  obtain ⟨t, ht⟩ := exists_nat_gt (1 / ε)
  have htpos : 0 < t := by
    have h : (0 : ℝ) < t := lt_trans (by positivity) ht
    exact_mod_cast h
  let k : ℕ := 2 ^ (t + 1)
  have hpow : 1 < 2 ^ t := one_lt_pow₀ (by omega : 1 < (2 : ℕ)) (by omega)
  have hk : 3 ≤ k := by
    dsimp [k]
    rw [pow_succ]
    omega
  have hdigit : 2 ^ t ≤ k - 1 := by
    dsimp [k]
    rw [pow_succ]
    omega
  let d : ℝ := ((k - 1 : ℕ) : ℝ)
  let L : ℝ := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hd : (0 : ℝ) < d := by
    dsimp [d]
    exact_mod_cast (by omega : 0 < k - 1)
  have hlognum : (t : ℝ) * L ≤ Real.log d := by
    have hdreal : (2 : ℝ) ^ t ≤ d := by
      dsimp [d]
      exact_mod_cast hdigit
    calc
      (t : ℝ) * L = Real.log ((2 : ℝ) ^ t) := by rw [Real.log_pow]
      _ ≤ Real.log d := Real.log_le_log (by positivity) hdreal
  have hkreal : (k : ℝ) = (2 : ℝ) ^ (t + 1) := by simp [k]
  have hlogden : Real.log ((k : ℝ) ^ 2) = 2 * ((t : ℝ) + 1) * L := by
    rw [Real.log_pow, hkreal, Real.log_pow]
    push_cast
    ring
  have hdenpos : 0 < 2 * ((t : ℝ) + 1) * L := by positivity
  have hratio : (t : ℝ) / (2 * ((t : ℝ) + 1)) ≤ growthExponent k := by
    unfold growthExponent
    rw [hlogden]
    have hdiv : (t : ℝ) * L / (2 * ((t : ℝ) + 1) * L) ≤
        Real.log d / (2 * ((t : ℝ) + 1) * L) :=
      div_le_div_of_nonneg_right hlognum hdenpos.le
    have hcancel : (t : ℝ) / (2 * ((t : ℝ) + 1)) =
        (t : ℝ) * L / (2 * ((t : ℝ) + 1) * L) := by
      field_simp [ne_of_gt hL]
    rw [hcancel]
    simpa [d] using hdiv
  have htprod : 1 < (t : ℝ) * ε := (div_lt_iff₀ hε).1 ht
  have hgap : 1 / (2 * ((t : ℝ) + 1)) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * ((t : ℝ) + 1))).2
    nlinarith
  have hidentity : (t : ℝ) / (2 * ((t : ℝ) + 1)) =
      1 / 2 - 1 / (2 * ((t : ℝ) + 1)) := by
    field_simp
    ring
  refine ⟨k, hk, ?_⟩
  rw [hidentity] at hratio
  linarith

/-- Lower-bound half of the growth exponent: for every positive error,
all sufficiently large radii admit a measurable integer-distance-avoiding set
with area at least a constant times `R^(1/2 - ε)`. -/
theorem erdos953_lower :
    ∀ ε : ℝ, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
        ∀ R : ℝ, R₀ ≤ R →
          ∃ A : Set Plane,
            MeasurableSet A ∧
            A ⊆ Metric.ball (0 : Plane) R ∧
            (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
              ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ)) ∧
            c * R ^ (1 / 2 - ε) ≤ (MeasureTheory.volume A).toReal := by
  intro ε hε
  obtain ⟨k, hk, hsk⟩ := exists_growthExponent_gt_half_sub ε hε
  obtain ⟨c, hc, hfixed⟩ := digitDisks_lower_growth_fixed_base k hk
  refine ⟨c, hc, 16 * (k : ℝ) ^ 2 + 1, ?_⟩
  intro R hR
  obtain ⟨A, hmeas, hsubset, hno, harea⟩ := hfixed R hR
  have hR1 : (1 : ℝ) ≤ R := by
    have hK : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith [sq_nonneg (k : ℝ)]
  have hpow : R ^ (1 / 2 - ε) ≤ R ^ growthExponent k :=
    Real.rpow_le_rpow_of_exponent_le hR1 hsk.le
  refine ⟨A, hmeas, hsubset, hno, ?_⟩
  exact (mul_le_mul_of_nonneg_left hpow hc.le).trans harea

#print axioms erdos953_lower
#print axioms digitDisks_lower_growth_explicit
#print axioms growthExponent_ge_half_sub_inv
#print axioms exp_neg_one_mul_sqrt_le_rpow_growthExponent
#print axioms digitDisks_lower_sqrt_with_base

end Erdos953Lower
