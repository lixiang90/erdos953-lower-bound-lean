import Erdos953Lower.RetreatGeometry

namespace Erdos953Lower
open Finset
noncomputable section
set_option maxHeartbeats 800000

/-- Leading signed digit control with a trimmed alphabet. -/
theorem trimmed_leading_bounds (k t i : ℕ) (d : ℕ → ℤ)
    (hk : 8 ≤ k) (ht : 1 ≤ t) (htk : 2*t ≤ k)
    (hbound : ∀ j ≤ i, |d j| ≤ (k : ℤ) - t - 1) (hdi : d i ≠ 0) :
    let D : ℝ := (|d i| : ℤ)
    let X : ℝ := (k : ℝ)^i
    let a : ℝ := (k : ℝ) * (|∑ j ∈ range (i+1), d j * ((k : ℤ)^2)^j| : ℤ)
    let b : ℝ := (|∑ j ∈ range (i+1), d j * (k : ℤ)^j| : ℤ)
    1 ≤ D ∧ D ≤ (k : ℝ)-2 ∧ 1 ≤ X ∧ 1 ≤ a ∧ 1 ≤ b ∧
      b ≤ (D+1)*X ∧ (8/9 : ℝ)*(k : ℝ)*D*X^2 ≤ a ∧
      a ≤ (k : ℝ)*(D+1/9)*X^2 ∧
      (i = 0 → a = (k : ℝ)*D ∧ b = D) ∧
      (0 < i → D*(t : ℝ)*(k : ℝ)^(i-1)+1 ≤ b) := by
  let K : ℤ := k
  let C : ℤ := K - t - 1
  let S : ℤ := ∑ j ∈ range i, K^j
  let T : ℤ := ∑ j ∈ range i, d j * K^j
  let U : ℤ := ∑ j ∈ range (i+1), d j * K^j
  let V : ℤ := ∑ j ∈ range i, (K^2)^j
  let W : ℤ := ∑ j ∈ range i, d j * (K^2)^j
  let Q : ℤ := ∑ j ∈ range (i+1), d j * (K^2)^j
  let D : ℤ := |d i|
  have hK : 8 ≤ K := by dsimp [K]; exact_mod_cast hk
  have hK0 : 0 ≤ K := by omega
  have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have htk' : 2*(t : ℤ) ≤ K := by dsimp [K]; exact_mod_cast htk
  have hC0 : 0 ≤ C := by dsimp [C]; omega
  have hD1 : 1 ≤ D := by dsimp [D]; have := abs_pos.mpr hdi; omega
  have hDK : D ≤ K-2 := by have := hbound i le_rfl; dsimp [D, C, K] at *; omega
  have hS0 : 0 ≤ S := by dsimp [S]; exact sum_nonneg (fun j _ => pow_nonneg hK0 j)
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hX0 : 0 ≤ K^i := pow_nonneg hK0 i
  have hX1 : 1 ≤ K^i := one_le_pow₀ (by omega)
  have hgeom : S*(K-1)+1 = K^i := by
    simpa [S] using geom_sum_mul_add (K-1) i
  have hgeomQ : V*(K^2-1)+1 = (K^2)^i := by
    have hh := geom_sum_mul_add (K^2-1) i
    rw [show K^2-1+1 = K^2 by ring] at hh
    exact hh
  have hT := weighted_digit_sum_abs_le K C i d hK0 (fun j hj => hbound j hj.le)
  have hW := weighted_digit_sum_abs_le (K^2) C i d (sq_nonneg K)
    (fun j hj => hbound j hj.le)
  change |T| ≤ C*S at hT
  change |W| ≤ C*V at hW
  have hsum : U = T + d i * K^i := by simp [U, T, sum_range_succ]
  have hsumQ : Q = W + d i * (K^2)^i := by simp [Q, W, sum_range_succ]
  have hu : |U| ≤ |T|+D*K^i := by
    simpa only [hsum, abs_mul, abs_of_nonneg hX0] using abs_add_le T (d i*K^i)
  have hu' : D*K^i ≤ |U|+|T| := by
    calc
      D*K^i = |d i*K^i| := by rw [abs_mul, abs_of_nonneg hX0]
      _ = |U-T| := by rw [hsum]; congr 1; ring
      _ ≤ |U|+|T| := abs_sub _ _
  have hq : |Q| ≤ |W|+D*(K^2)^i := by
    calc
      |Q| = |W+d i*(K^2)^i| := congrArg abs hsumQ
      _ ≤ |W|+|d i*(K^2)^i| := abs_add_le _ _
      _ = |W|+D*(K^2)^i := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (sq_nonneg K) i)]
  have hq' : D*(K^2)^i ≤ |Q|+|W| := by
    calc
      D*(K^2)^i = |d i*(K^2)^i| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (sq_nonneg K) i)]
      _ = |Q-W| := by rw [hsumQ]; congr 1; ring
      _ ≤ |Q|+|W| := abs_sub _ _
  have htail : |T| ≤ K^i := by
    have hCS := mul_le_mul_of_nonneg_right (show C ≤ K-1 by dsimp [C]; omega) hS0
    nlinarith only [hT, hCS, hgeom]
  have hqcoef : 9*C ≤ K^2-1 := by
    dsimp [C]
    nlinarith only [hK, ht']
  have hqtail : 9*|W| ≤ (K^2)^i := by
    have hh := mul_le_mul_of_nonneg_right hqcoef hV0
    linarith only [hh, hW, hgeomQ]
  have hu1 : 1 ≤ |U| := by
    have hDd := mul_nonneg (show 0 ≤ D-1 by omega) hX0
    have hCS := mul_le_mul_of_nonneg_right (show C ≤ K-1 by dsimp [C]; omega) hS0
    nlinarith only [hu', hT, hgeom, hDd, hCS]
  have hqlo : 8*D*(K^2)^i ≤ 9*|Q| := by
    have hh := mul_nonneg (show 0 ≤ D-1 by omega) (pow_nonneg (sq_nonneg K) i)
    nlinarith only [hq', hqtail, hh]
  have hqhi : 9*|Q| ≤ (9*D+1)*(K^2)^i := by linarith only [hq, hqtail]
  have hq1 : 1 ≤ |Q| := by
    have hp : 1 ≤ (K^2)^i := one_le_pow₀ (by nlinarith only [hK])
    nlinarith only [hqlo, hD1, hp]
  have hmullo := mul_le_mul_of_nonneg_left hqlo hK0
  have hmulhi := mul_le_mul_of_nonneg_left hqhi hK0
  have hpow : (K^2)^i = (K^i)^2 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
  rw [hpow] at hmullo hmulhi
  have hA1 : 1 ≤ K*|Q| := by nlinarith only [hK, hq1]
  have hbhi : |U| ≤ (D+1)*K^i := by nlinarith only [hu, htail]
  have hXreal : (1 : ℝ) ≤ (k : ℝ)^i := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ k))
  refine ⟨by exact_mod_cast hD1, by exact_mod_cast hDK, hXreal,
    by exact_mod_cast hA1, by exact_mod_cast hu1, by exact_mod_cast hbhi, ?_, ?_, ?_, ?_⟩
  · have hh : (K : ℝ) * (8*(D : ℝ)*((K : ℝ)^i)^2) ≤
        (K : ℝ)*(9*(|Q| : ℤ)) := by exact_mod_cast hmullo
    dsimp [K, Q, D] at hh ⊢
    push_cast at hh ⊢
    nlinarith only [hh]
  · have hh : (K : ℝ)*(9*(|Q| : ℤ)) ≤
        (K : ℝ)*((9*(D : ℝ)+1)*((K : ℝ)^i)^2) := by exact_mod_cast hmulhi
    dsimp [K, Q, D] at hh ⊢
    push_cast at hh ⊢
    nlinarith only [hh]
  · intro hi
    subst i
    simp [D]
  · intro hi
    have he : i = (i-1)+1 := by omega
    have hp : K^i = K*K^(i-1) := by
      calc
        K^i = K^((i-1)+1) := congrArg (fun z => K^z) he
        _ = K*K^(i-1) := by rw [pow_succ]; ring
    have hS : K^(i-1) ≤ S := by
      exact single_le_sum (fun j _ => pow_nonneg hK0 j) (mem_range.mpr (by omega))
    have hlead : (D-1)*K^i+(t : ℤ)*S+1 ≤ |U| := by
      dsimp [C] at hT
      nlinarith only [hu', hT, hgeom]
    have hh1 := mul_le_mul_of_nonneg_left hS (show 0 ≤ (t : ℤ) by omega)
    have hh2 := mul_nonneg (show 0 ≤ D-1 by omega)
      (mul_nonneg (show 0 ≤ K-(t : ℤ) by omega) (pow_nonneg hK0 (i-1)))
    have hres : D*(t : ℤ)*K^(i-1)+1 ≤ |U| := by
      rw [hp] at hlead
      nlinarith only [hlead, hh1, hh2]
    exact_mod_cast hres

theorem trimmed_rectangle_bounds (k t i : ℕ) (d : ℕ → ℤ)
    (hk : 8 ≤ k) (ht : 1 ≤ t) (htk : 2*t ≤ k)
    (hbound : ∀ j ≤ i, |d j| ≤ (k : ℤ)-t-1) (hdi : d i ≠ 0) :
    let a : ℝ := (k : ℝ) * (|∑ j ∈ range (i+1), d j*((k : ℤ)^2)^j| : ℤ)
    let b : ℝ := (|∑ j ∈ range (i+1), d j*(k : ℤ)^j| : ℤ)
    1 ≤ a ∧ 1 ≤ b ∧ 2*a*retreatHeight k t < (b-1/2)^2 ∧
      (b+1/2)^2 ≤ (45/32 : ℝ)*a := by
  let D : ℝ := (|d i| : ℤ)
  let X : ℝ := (k : ℝ)^i
  let a : ℝ := (k : ℝ) * (|∑ j ∈ range (i+1), d j*((k : ℤ)^2)^j| : ℤ)
  let b : ℝ := (|∑ j ∈ range (i+1), d j*(k : ℤ)^j| : ℤ)
  obtain ⟨hD1,hDK,hX1,ha1,hb1,hbhi,halo,hahi,hzero,hpos⟩ :=
    trimmed_leading_bounds k t i d hk ht htk hbound hdi
  change 1 ≤ D at hD1
  change D ≤ (k : ℝ)-2 at hDK
  change 1 ≤ X at hX1
  change 1 ≤ a at ha1
  change 1 ≤ b at hb1
  change b ≤ (D+1)*X at hbhi
  change (8/9 : ℝ)*(k : ℝ)*D*X^2 ≤ a at halo
  change a ≤ (k : ℝ)*(D+1/9)*X^2 at hahi
  have hK : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hK0 : (0 : ℝ) < k := by linarith
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hH := retreatHeight_bounds k t hk ht
  refine ⟨ha1,hb1,?_,?_⟩
  · change 2*a*retreatHeight k t < (b-1/2)^2
    by_cases hi : i = 0
    · obtain ⟨ha,hb⟩ := hzero hi
      change a = (k : ℝ)*D at ha
      change b = D at hb
      rw [ha,hb]
      exact retreat_lower_zero (k : ℝ) (t : ℝ) D (retreatHeight k t) hK ht0.le
        (by exact_mod_cast htk) hD1 hH.2.2
    · have hi0 : 0 < i := by omega
      let L : ℝ := (t : ℝ)*(k : ℝ)^(i-1)
      have hL : 0 < L := by dsimp [L]; positivity
      have hp : X = (k : ℝ)*(k : ℝ)^(i-1) := by
        dsimp [X]
        calc
          (k : ℝ)^i = (k : ℝ)^((i-1)+1) := by congr 1; omega
          _ = (k : ℝ)*(k : ℝ)^(i-1) := by rw [pow_succ]; ring
      have hfirst := mul_le_mul_of_nonneg_right hahi
        (show 0 ≤ 2*retreatHeight k t by positivity [hH.1])
      have hsecond := mul_le_mul_of_nonneg_left hH.2.2
        (show 0 ≤ 2*(k : ℝ)*(D+1/9)*X^2 by positivity)
      have he : (2*(k : ℝ)*(D+1/9)*X^2) *
          (4*(t : ℝ)^2/(9*(k : ℝ)^3)) = (8/9 : ℝ)*(D+1/9)*L^2 := by
        rw [hp]
        dsimp [L]
        field_simp
        <;> ring
      rw [he] at hsecond
      have haH : 2*a*retreatHeight k t ≤ (8/9 : ℝ)*(D+1/9)*L^2 := by
        nlinarith only [hfirst,hsecond]
      have hbL : D*L+1 ≤ b := by
        dsimp [L,D,b]
        nlinarith only [hpos hi0]
      exact retreat_lower_leading D L a b (retreatHeight k t) hD1 hL hbL haH
  · have hb : b+1/2 ≤ (D+3/2)*X := by nlinarith only [hbhi,hX1]
    have hbsq : (b+1/2)^2 ≤ ((D+3/2)*X)^2 := by
      exact pow_le_pow_left₀ (by linarith only [hb1]) hb 2
    have hquad := mul_le_mul_of_nonneg_right
      (retreat_digit_quadratic (k : ℝ) D hK hD1 hDK) (sq_nonneg X)
    have hcoef : ((k : ℝ)+2)*D*X^2 ≤
        (45/32 : ℝ)*((8/9 : ℝ)*(k : ℝ)*D*X^2) := by
      have hh := mul_nonneg (show 0 ≤ (k : ℝ)-8 by linarith)
        (show 0 ≤ D*X^2 by positivity)
      nlinarith only [hh]
    have hlast := mul_le_mul_of_nonneg_left halo (by norm_num : (0 : ℝ) ≤ 45/32)
    nlinarith only [hbsq,hquad,hcoef,hlast]

#print axioms trimmed_rectangle_bounds
end
end Erdos953Lower
