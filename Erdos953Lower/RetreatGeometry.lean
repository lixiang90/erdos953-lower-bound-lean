import Erdos953Lower.AnisotropicRectangles

/-!
Geometry of the trimmed, vertically compressed digit construction.
All rectangles have full width 1/2 and full height at most 1/256.
The estimates below concern entire rectangles, not just their centres.
-/
namespace Erdos953Lower
open MeasureTheory
noncomputable section
set_option maxHeartbeats 600000

def retreatHeight (k t : ℕ) : ℝ :=
  min (1 / 256) (4 * (t : ℝ) ^ 2 / (9 * (k : ℝ) ^ 3))

def wideRectangle (p : Plane) (H : ℝ) : Set Plane :=
  {x | |x 0 - p 0| < 1 / 4 ∧ |x 1 - p 1| < H / 2}

theorem retreatHeight_bounds (k t : ℕ) (hk : 8 ≤ k) (ht : 1 ≤ t) :
    0 < retreatHeight k t ∧ retreatHeight k t ≤ 1 / 256 ∧
      retreatHeight k t ≤ 4 * (t : ℝ)^2 / (9 * (k : ℝ)^3) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  exact ⟨lt_min (by norm_num) (by positivity), min_le_left _ _, min_le_right _ _⟩

theorem retreatHeight_two (k : ℕ) (hk : 8 ≤ k) :
    retreatHeight k 2 = 16 / (9 * (k : ℝ)^3) := by
  have hk8 : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hk8 3
  unfold retreatHeight
  norm_num only
  rw [min_eq_right]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 9 * (k : ℝ)^3)
    (by norm_num : (0 : ℝ) < 256)).2
  norm_num at hp ⊢
  linarith

theorem wideRectangle_measurable (p : Plane) (H : ℝ) :
    MeasurableSet (wideRectangle p H) := by
  have h0 : Continuous (fun x : Plane => x 0) := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous (fun x : Plane => x 1) := PiLp.continuous_apply 2 _ 1
  exact ((isOpen_lt (h0.sub continuous_const).abs continuous_const).inter
    (isOpen_lt (h1.sub continuous_const).abs continuous_const)).measurableSet

theorem wideRectangle_volume (p : Plane) (H : ℝ) :
    volume (wideRectangle p H) = ENNReal.ofReal (H / 2) := by
  let h : Fin 2 → ℝ := fun i => if i = 0 then 1 / 4 else H / 2
  have hpre : WithLp.toLp 2 ⁻¹' wideRectangle p H =
      Set.pi Set.univ (fun i => Set.Ioo (p i - h i) (p i + h i)) := by
    ext x
    simp only [Set.mem_preimage, wideRectangle, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, forall_const, Fin.forall_fin_two, Set.mem_Ioo]
    dsimp [h]
    simp only [abs_lt]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    (wideRectangle_measurable p H).nullMeasurableSet, hpre, Real.volume_pi_Ioo]
  simp only [Fin.prod_univ_two]
  dsimp [h]
  have h0 : p 0 + 1 / 4 - (p 0 - 1 / 4) = (1 / 2 : ℝ) := by ring
  have h1 : p 1 + H / 2 - (p 1 - H / 2) = H := by ring
  rw [h0, h1, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

theorem wideRectangle_diameter (p : Plane) (H : ℝ) (hH : H ≤ 1 / 256)
    {x y : Plane} (hx : x ∈ wideRectangle p H) (hy : y ∈ wideRectangle p H) :
    dist x y < 1 := by
  have h0 := coordinate_perturbation (x 0) (y 0) (p 0) (p 0) (1 / 4) hx.1 hy.1
  have h1 := coordinate_perturbation (x 1) (y 1) (p 1) (p 1) (H / 2) hx.2 hy.2
  simp only [sub_self, abs_zero, sub_zero, abs_abs] at h0 h1
  rw [plane_dist_coordinates]
  have hs := Real.sq_sqrt (show 0 ≤ (x 0 - y 0)^2 + (x 1 - y 1)^2 by positivity)
  have hs0 := Real.sqrt_nonneg ((x 0 - y 0)^2 + (x 1 - y 1)^2)
  have hsq0 : (x 0 - y 0)^2 ≤ (1 / 2 : ℝ)^2 := by
    nlinarith [abs_nonneg (x 0 - y 0), sq_abs (x 0 - y 0)]
  have hsq1 : (x 1 - y 1)^2 ≤ (1 / 256 : ℝ)^2 := by
    nlinarith [abs_nonneg (x 1 - y 1), sq_abs (x 1 - y 1)]
  nlinarith only [hs, hs0, hsq0, hsq1]

/-- The convex quadratic has the same value at both endpoints. -/
theorem retreat_digit_quadratic (K d : ℝ) (hK : 8 ≤ K)
    (hd : 1 ≤ d) (hdK : d ≤ K - 2) :
    (d + 3 / 2)^2 ≤ (K + 2) * d := by
  have hp := mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hdK)
  nlinarith only [hp, hK]

theorem retreat_lower_leading (d L a b H : ℝ) (hd : 1 ≤ d) (hL : 0 < L)
    (hb : d * L + 1 ≤ b)
    (haH : 2 * a * H ≤ (8 / 9 : ℝ) * (d + 1 / 9) * L^2) :
    2 * a * H < (b - 1 / 2)^2 := by
  have hcoef : (1 / 81 : ℝ) ≤ d^2 - (8 / 9) * (d + 1 / 9) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ d - 1)
      (by linarith : 0 ≤ d + 1 / 9)]
  have hL0 := hL.le
  have hdb : 0 ≤ d * L := by positivity
  have hsq : (d * L)^2 ≤ (b - 1 / 2)^2 := by
    nlinarith [sq_nonneg (b - 1 / 2 - d * L)]
  have hscale := mul_le_mul_of_nonneg_right hcoef (sq_nonneg L)
  nlinarith only [hscale, hsq, haH, sq_pos_of_pos hL]

theorem retreat_lower_zero (K t d H : ℝ) (hK : 8 ≤ K)
    (ht : 0 ≤ t) (htK : 2 * t ≤ K) (hd : 1 ≤ d)
    (hH : H ≤ 4 * t^2 / (9 * K^3)) :
    2 * (K * d) * H < (d - 1 / 2)^2 := by
  have hK0 : 0 < K := by linarith
  have ht2 : 4 * t^2 ≤ K^2 := by nlinarith [sq_nonneg (K - 2*t)]
  have hmul := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 2 * (K*d))
  have hcancel : 2 * (K*d) * (4*t^2 / (9*K^3)) =
      (2*d/9) * (4*t^2/K^2) := by field_simp <;> ring
  rw [hcancel] at hmul
  have hratio : 4*t^2/K^2 ≤ 1 := (div_le_one (by positivity)).2 ht2
  have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2*d/9)
  have hds : d/36 ≤ (d - 1/2)^2 - 2*d/9 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ d-1) (by linarith : 0 ≤ d)]
  nlinarith only [hmul, hh, hds, hd]

/-- A positive integer vertical difference places the full distance strictly
between consecutive integers. -/
theorem retreat_sqrt_between (a b H u v : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hH0 : 0 ≤ H) (hH : H ≤ 1 / 256)
    (hlower : 2*a*H < (b - 1/2)^2)
    (hupper : (b + 1/2)^2 ≤ (45/32 : ℝ)*a)
    (hu : |u| ≤ 1/2) (hv : |v| ≤ H) :
    a < Real.sqrt ((a+v)^2+(b+u)^2) ∧
      Real.sqrt ((a+v)^2+(b+u)^2) < a+1 := by
  have huv := abs_le.mp hu
  have hvv := abs_le.mp hv
  have hsmall : H^2 < 1 := by nlinarith
  have hlo : (b-1/2)^2 ≤ (b+u)^2 := by
    nlinarith [sq_nonneg (b+u-(b-1/2))]
  have hhi : (b+u)^2 ≤ (b+1/2)^2 := by
    nlinarith [sq_nonneg (b+1/2-(b+u))]
  have hvlo : (a-H)^2 ≤ (a+v)^2 := by
    nlinarith [sq_nonneg (a+v-(a-H))]
  have hvhi : (a+v)^2 ≤ (a+H)^2 := by
    nlinarith [sq_nonneg (a+H-(a+v))]
  have hprod := mul_le_mul_of_nonneg_left hH (by linarith : 0 ≤ 2*a)
  have hs := Real.sq_sqrt (show 0 ≤ (a+v)^2+(b+u)^2 by positivity)
  have hs0 := Real.sqrt_nonneg ((a+v)^2+(b+u)^2)
  constructor <;> nlinarith only [ha, hs, hs0, hlo, hhi, hvlo, hvhi,
    hlower, hupper, hprod, hsmall, sq_nonneg H]

theorem retreat_cross_sqrt_between (a b u v : ℝ)
    (ha : 1 ≤ a) (hb : 48 ≤ b) (hba : b^2 ≤ a) (hab : a ≤ 32*b^2)
    (hu : |u| ≤ 1/2) (hv : |v| ≤ 1/256) :
    a+1/512 < Real.sqrt ((a+v)^2+(b+u)^2) ∧
      Real.sqrt ((a+v)^2+(b+u)^2) < a+1-1/512 := by
  have huv := abs_le.mp hu
  have hvv := abs_le.mp hv
  have hb0 : 0 ≤ b := by linarith
  have hl : (95/96 : ℝ)*b ≤ b+u := by linarith
  have hh : b+u ≤ (97/96 : ℝ)*b := by linarith
  have hls := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (95/96)*b) hl 2
  have hhs := pow_le_pow_left₀ (by linarith : 0 ≤ b+u) hh 2
  have hvl := pow_le_pow_left₀ (by linarith : 0 ≤ a-1/256)
    (show a-1/256 ≤ a+v by linarith) 2
  have hvh := pow_le_pow_left₀ (by linarith : 0 ≤ a+v)
    (show a+v ≤ a+1/256 by linarith) 2
  have hs := Real.sq_sqrt (show 0 ≤ (a+v)^2+(b+u)^2 by positivity)
  have hs0 := Real.sqrt_nonneg ((a+v)^2+(b+u)^2)
  constructor
  · nlinarith only [hs,hs0,hls,hvl,hab,ha,sq_nonneg b]
  · nlinarith only [hs,hs0,hhs,hvh,hba,ha]

/-- The simple prefix rectangle lies below the horizontal axis. -/
theorem retreat_base_sqrt_between (a b u v : ℝ)
    (ha : 1 ≤ a) (hb : 64 ≤ b) (hba : 48*b^2 ≤ 25*a)
    (hu : |u| ≤ 5/8) (hvlo : 15/512 ≤ v) (hvhi : v ≤ 273/512) :
    a < Real.sqrt ((a+v)^2+(b+u)^2) ∧
      Real.sqrt ((a+v)^2+(b+u)^2) < a+1 := by
  have huv := abs_le.mp hu
  have hl := pow_le_pow_left₀ (by linarith : 0 ≤ a)
    (show a < a+v by linarith).le 2
  have hb0 : 0 ≤ b := by linarith
  have hh : b+u ≤ (517/512 : ℝ)*b := by linarith
  have hhs := pow_le_pow_left₀ (by linarith : 0 ≤ b+u) hh 2
  have hvh := pow_le_pow_left₀ (by linarith : 0 ≤ a+v)
    (show a+v ≤ a+273/512 by linarith) 2
  have hprod := mul_nonneg (show 0 ≤ a by linarith) (show 0 < v by linarith).le
  have hs := Real.sq_sqrt (show 0 ≤ (a+v)^2+(b+u)^2 by positivity)
  have hs0 := Real.sqrt_nonneg ((a+v)^2+(b+u)^2)
  constructor
  · nlinarith only [hs,hs0,hl,hvlo,ha,hprod,sq_nonneg (b+u)]
  · nlinarith only [hs,hs0,hhs,hvh,hba,ha]

theorem retreat_frame_difference (B C x y X Y : ℝ)
    (hB : 128 ≤ B) (hC : 64 ≤ C) (hCB : 2*C ≤ B)
    (hx : B ≤ x) (hx' : x ≤ 5*B/4) (hy : 3*B^2 ≤ y) (hy' : y ≤ 7*B^2/2)
    (hX : C ≤ X) (hX' : X ≤ 5*C/4) (hY : 3*C^2 ≤ Y) (hY' : Y ≤ 7*C^2/2) :
    1 ≤ y-Y ∧ 48 ≤ x-X ∧ (x-X)^2 ≤ y-Y ∧ y-Y ≤ 32*(x-X)^2 := by
  have hB0 : 0 ≤ B := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hCsq := pow_le_pow_left₀ (show 0 ≤ 2*C by positivity) hCB 2
  have hbLo : 3*B/8 ≤ x-X := by linarith only [hx,hX',hCB]
  have hbHi : x-X ≤ 5*B/4 := by linarith only [hx',hX,hC]
  have haLo : 17*B^2/8 ≤ y-Y := by nlinarith only [hy,hY',hCsq]
  have haHi : y-Y ≤ 7*B^2/2 := by nlinarith only [hy',hY,sq_nonneg C]
  have hbsLo := pow_le_pow_left₀ (show 0 ≤ 3*B/8 by positivity) hbLo 2
  have hbsHi := pow_le_pow_left₀ (by linarith only [hbLo,hB]) hbHi 2
  exact ⟨by nlinarith only [haLo,hB], by linarith only [hbLo,hB],
    by nlinarith only [haLo,hbsHi,sq_nonneg B],
    by nlinarith only [haHi,hbsLo,sq_nonneg B]⟩

#print axioms retreat_cross_sqrt_between
#print axioms retreat_base_sqrt_between
#print axioms retreat_sqrt_between
#print axioms retreat_lower_leading
#print axioms wideRectangle_volume
end
end Erdos953Lower
