import Erdos953Lower.RetreatRectangles
import Erdos953Lower.RetreatParameters

namespace Erdos953Lower
open MeasureTheory
noncomputable section
set_option maxHeartbeats 1000000

def retreatBase : Set Plane := {x | |x 0| < 3/8 ∧ |x 1+9/32| < 1/4}

theorem retreatBase_measurable : MeasurableSet retreatBase := by
  have h0 : Continuous (fun x : Plane => x 0) := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous (fun x : Plane => x 1) := PiLp.continuous_apply 2 _ 1
  exact ((isOpen_lt h0.abs continuous_const).inter
    (isOpen_lt (h1.add continuous_const).abs continuous_const)).measurableSet

theorem retreatBase_volume : volume retreatBase = ENNReal.ofReal (3/8 : ℝ) := by
  let p : Plane := !₂[0, -(9/32 : ℝ)]
  let h : Fin 2 → ℝ := fun i => if i = 0 then 3/8 else 1/4
  have hp : WithLp.toLp 2 ⁻¹' retreatBase =
      Set.pi Set.univ (fun i => Set.Ioo (p i-h i) (p i+h i)) := by
    ext x
    simp only [Set.mem_preimage,retreatBase,Set.mem_setOf_eq,Set.mem_pi,Set.mem_univ,
      forall_const,Fin.forall_fin_two,Set.mem_Ioo]
    dsimp [p,h]
    simp only [abs_lt]
    constructor
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
      exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
      exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    retreatBase_measurable.nullMeasurableSet,hp,Real.volume_pi_Ioo]
  simp only [Fin.prod_univ_two]
  norm_num [p,h]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3/4)]
  norm_num

theorem retreatBase_diameter {x y : Plane} (hx : x ∈ retreatBase) (hy : y ∈ retreatBase) :
    dist x y < 1 := by
  have h0 : |x 0-y 0| < 3/4 := by
    have hh := abs_sub (x 0) (y 0)
    linarith only [hh,hx.1,hy.1]
  have h1 : |x 1-y 1| < 1/2 := by
    have hh := abs_sub (x 1+9/32) (y 1+9/32)
    rw [show x 1+9/32-(y 1+9/32)=x 1-y 1 by ring] at hh
    linarith only [hh,hx.2,hy.2]
  rw [plane_dist_coordinates]
  have hs := Real.sq_sqrt (show 0 ≤ (x 0-y 0)^2+(x 1-y 1)^2 by positivity)
  have hs0 := Real.sqrt_nonneg ((x 0-y 0)^2+(x 1-y 1)^2)
  have hsq0 : (x 0-y 0)^2 ≤ (3/4 : ℝ)^2 := by
    nlinarith [abs_nonneg (x 0-y 0),sq_abs (x 0-y 0)]
  have hsq1 : (x 1-y 1)^2 ≤ (1/2 : ℝ)^2 := by
    nlinarith [abs_nonneg (x 1-y 1),sq_abs (x 1-y 1)]
  nlinarith only [hs,hs0,hsq0,hsq1]

theorem retreatBase_subset_unit_ball : retreatBase ⊆ Metric.ball (0 : Plane) 1 := by
  intro x hx
  have hy := abs_lt.mp hx.2
  have hyabs : |x 1| ≤ 17/32 := by rw [abs_le]; constructor <;> linarith
  have hxabs : |x 0| ≤ 3/8 := hx.1.le
  apply Metric.mem_ball.mpr
  rw [plane_dist_coordinates]
  simp only [PiLp.zero_apply,sub_zero]
  have hs := Real.sq_sqrt (show 0 ≤ (x 0)^2+(x 1)^2 by positivity)
  have hs0 := Real.sqrt_nonneg ((x 0)^2+(x 1)^2)
  have hsq0 : (x 0)^2 ≤ (3/8 : ℝ)^2 := by nlinarith [abs_nonneg (x 0),sq_abs (x 0)]
  have hsq1 : (x 1)^2 ≤ (17/32 : ℝ)^2 := by nlinarith [abs_nonneg (x 1),sq_abs (x 1)]
  nlinarith only [hs,hs0,hsq0,hsq1]

def tailParameters (j : ℕ) (hj : 14 ≤ j) : RetreatParameters j := chosenParameters j (by omega)
def tailTrim (j : ℕ) (hj : 14 ≤ j) : ℕ :=
  optimalTrim (tailParameters j hj).k (tailParameters j hj).n
    (retreat_parameter_k_ge_eight (tailParameters j hj) hj)

theorem tailTrim_spec (j : ℕ) (hj : 14 ≤ j) :
    1 ≤ tailTrim j hj ∧ 2*tailTrim j hj ≤ (tailParameters j hj).k := by
  exact ⟨(optimalTrim_spec _ _ _).1,(optimalTrim_spec _ _ _).2.1⟩

def tailGeneration (j : ℕ) (hj : 14 ≤ j) : Set Plane :=
  retreatRectangles (tailParameters j hj).k (tailTrim j hj) (tailParameters j hj).n
    (tailTrim_spec j hj).1 ((2 : ℤ)^j) (3*((2 : ℤ)^j)^2)

def retreatInfinity : Set Plane := retreatBase ∪ ⋃ j : {j : ℕ // 14 ≤ j}, tailGeneration j.val j.property

theorem tailGeneration_measurable (j : ℕ) (hj : 14 ≤ j) : MeasurableSet (tailGeneration j hj) :=
  retreatRectangles_measurable _ _ _ _ _ _

theorem retreatInfinity_measurable : MeasurableSet retreatInfinity :=
  retreatBase_measurable.union (MeasurableSet.iUnion (fun j => tailGeneration_measurable j.val j.property))

theorem retreatPoint_frame (k t n : ℕ) (hk : 8 ≤ k) (ht : 1 ≤ t)
    (B : ℤ) (hB : 64 ≤ B) (hfit : (k : ℝ)^(2*n) ≤ (B : ℝ)^2/16)
    (α : Fin n → Fin (k-t)) :
    let p := retreatPoint k t n ht B (3*B^2) α
    (B : ℝ) ≤ p 0 ∧ p 0 ≤ 5*(B : ℝ)/4 ∧
      3*(B : ℝ)^2 ≤ p 1 ∧ p 1 ≤ 7*(B : ℝ)^2/2 := by
  let α' := trimEmbed k t n ht α
  have hx := xCoord_bound k n (by omega) α'
  have hy := yCoord_bound_sharp k n (by omega) α'
  rw [yCoord_compressedY] at hy
  have hx0 : (0 : ℝ) ≤ (xCoord k n α' : ℤ) := by exact_mod_cast hx.1
  have hx1 : (xCoord k n α' : ℝ) < (k : ℝ)^n := by exact_mod_cast hx.2
  have hy0 : (0 : ℝ) ≤ (compressedY k n α' : ℤ) := by exact_mod_cast (by linarith only [hy.1] : 0 ≤ compressedY k n α')
  have hy1 : (compressedY k n α' : ℝ) < (k : ℝ)^(2*n) := by
    have hh : compressedY k n α' < ((k : ℤ)^2)^n := by linarith only [hy.2]
    have hp : ((k : ℝ)^2)^n = (k : ℝ)^(2*n) := by rw [pow_mul]
    rw [← hp]
    exact_mod_cast hh
  have hBr : (64 : ℝ) ≤ B := by exact_mod_cast hB
  have hxpow : (k : ℝ)^n ≤ (B : ℝ)/4 := by
    have hp : ((k : ℝ)^n)^2 = (k : ℝ)^(2*n) := by rw [← pow_mul]; congr 1; omega
    rw [← hp] at hfit
    nlinarith only [hfit,hBr,pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) n]
  simp only [retreatPoint_zero,retreatPoint_one,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_pow]
  change (B : ℝ) ≤ (B : ℝ)+(xCoord k n α' : ℤ) ∧
    (B : ℝ)+(xCoord k n α' : ℤ) ≤ 5*(B : ℝ)/4 ∧
    3*(B : ℝ)^2 ≤ 3*(B : ℝ)^2+(compressedY k n α' : ℤ) ∧ _
  exact ⟨by linarith only [hx0],by linarith only [hx1,hxpow],
    by linarith only [hy0],by nlinarith only [hy1,hfit,sq_nonneg (B : ℝ)]⟩

theorem tailGeneration_volume (j : ℕ) (hj : 14 ≤ j) :
    volume (tailGeneration j hj) = ENNReal.ofReal
      (retreatArea (tailParameters j hj).k (tailParameters j hj).n (tailTrim j hj)) :=
  retreatRectangles_volume _ _ _ (retreat_parameter_k_ge_eight (tailParameters j hj) hj)
    _ (tailTrim_spec j hj).2 _ _

def centreFrame (B : ℝ) (p : Plane) : Prop :=
  B ≤ p 0 ∧ p 0 ≤ 5*B/4 ∧ 3*B^2 ≤ p 1 ∧ p 1 ≤ 7*B^2/2

def framedRectanglePoint (B : ℝ) (x : Plane) : Prop :=
  ∃ p : Plane, ∃ a : ℤ, ∃ H : ℝ, p 1 = (a : ℝ) ∧
    0 < H ∧ H ≤ 1/256 ∧ centreFrame B p ∧ x ∈ wideRectangle p H

theorem tail_scale_ge (j : ℕ) (hj : 14 ≤ j) : (128 : ℝ) ≤ (2 : ℝ)^j := by
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
  norm_num at hp
  linarith only [hp]

theorem tailGeneration_framed (j : ℕ) (hj : 14 ≤ j) {x : Plane}
    (hx : x ∈ tailGeneration j hj) : framedRectanglePoint ((2 : ℝ)^j) x := by
  let P := tailParameters j hj
  let t := tailTrim j hj
  have ht := tailTrim_spec j hj
  have hk := retreat_parameter_k_ge_eight P hj
  change x ∈ retreatRectangles P.k t P.n ht.1 ((2 : ℤ)^j) (3*((2 : ℤ)^j)^2) at hx
  obtain ⟨α,hx⟩ := Set.mem_iUnion.mp hx
  let p := retreatPoint P.k t P.n ht.1 ((2 : ℤ)^j) (3*((2 : ℤ)^j)^2) α
  have hB : (64 : ℤ) ≤ (2 : ℤ)^j := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 6 ≤ j by omega)
    norm_num at hp
    exact hp
  have hcap : generationCapacity j = (((2 : ℤ)^j : ℤ) : ℝ)^2/16 := by
    simp only [Int.cast_pow,Int.cast_ofNat]
    unfold generationCapacity
    rw [show (4 : ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul]
    congr 1
    congr 1
    omega
  have hfit : (P.k : ℝ)^(2*P.n) ≤ (((2 : ℤ)^j : ℤ) : ℝ)^2/16 := by
    rw [← hcap]
    exact P.fit
  have hf := retreatPoint_frame P.k t P.n hk ht.1 ((2 : ℤ)^j) hB hfit α
  have hH := retreatHeight_bounds P.k t hk ht.1
  refine ⟨p,3*((2 : ℤ)^j)^2+compressedY P.k P.n (trimEmbed P.k t P.n ht.1 α),
    retreatHeight P.k t,?_,hH.1,hH.2.1,?_,hx⟩
  · exact retreatPoint_one _ _ _ _ _ _ _
  · simpa only [centreFrame,p,Int.cast_pow,Int.cast_ofNat] using hf

theorem coordinate_perturbation_mixed (x y p q r s : ℝ)
    (hx : |x-p| < r) (hy : |y-q| < s) :
    abs (abs (x-y)-abs (p-q)) < r+s := by
  calc
    abs (abs (x-y)-abs (p-q)) ≤ |(x-y)-(p-q)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |(x-p)-(y-q)| := by congr 1; ring
    _ ≤ |x-p|+|y-q| := abs_sub _ _
    _ < r+s := by linarith

theorem framed_cross_no_integer (B C : ℝ) (hB : 128 ≤ B) (hC : 64 ≤ C)
    (hCB : 2*C ≤ B) {x y : Plane}
    (hx : framedRectanglePoint B x) (hy : framedRectanglePoint C y)
    (m : ℕ) : dist x y ≠ (m : ℝ) := by
  obtain ⟨p,a,H,hpa,hH0,hH,hp,hx⟩ := hx
  obtain ⟨q,A,J,hqA,hJ0,hJ,hq,hy⟩ := hy
  let a' : ℝ := p 1-q 1
  let b' : ℝ := p 0-q 0
  have hd := retreat_frame_difference B C (p 0) (p 1) (q 0) (q 1)
    hB hC hCB hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
  change 1 ≤ a' ∧ 48 ≤ b' ∧ b'^2 ≤ a' ∧ a' ≤ 32*b'^2 at hd
  let u := |x 0-y 0|-b'
  let v := |x 1-y 1|-a'
  have hu : |u| ≤ 1/2 := by
    have hh := coordinate_perturbation_mixed _ _ _ _ _ _ hx.1 hy.1
    rw [abs_of_nonneg (show 0 ≤ p 0-q 0 by linarith only [hd.2.1])] at hh
    change |u| < 1/4+1/4 at hh
    linarith only [hh]
  have hv : |v| ≤ 1/256 := by
    have hh := coordinate_perturbation_mixed _ _ _ _ _ _ hx.2 hy.2
    rw [abs_of_nonneg (show 0 ≤ p 1-q 1 by linarith only [hd.1])] at hh
    change |v| < H/2+J/2 at hh
    linarith only [hh,hH,hJ]
  have hb := retreat_cross_sqrt_between a' b' u v hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 hu hv
  have he : Real.sqrt ((a'+v)^2+(b'+u)^2) = dist x y := by
    rw [plane_dist_coordinates]
    dsimp [u,v]
    congr 1
    simp only [add_sub_cancel,sq_abs]
    ring
  rw [he] at hb
  have ha' : a' = ((a-A : ℤ) : ℝ) := by dsimp [a']; rw [hpa,hqA]; push_cast; rfl
  rw [ha'] at hb
  intro heq
  rw [heq] at hb
  have hlo : a-A < (m : ℤ) := by
    have hh : ((a-A : ℤ) : ℝ) < m := by linarith only [hb.1]
    exact_mod_cast hh
  have hhi : (m : ℤ) < a-A+1 := by
    have hh : (m : ℝ) < ((a-A : ℤ) : ℝ)+1 := by linarith only [hb.2]
    exact_mod_cast hh
  omega

theorem framed_base_no_integer (B : ℝ) (hB : 64 ≤ B) {x y : Plane}
    (hx : framedRectanglePoint B x) (hy : y ∈ retreatBase) (m : ℕ) :
    dist x y ≠ (m : ℝ) := by
  obtain ⟨p,a,H,hpa,hH0,hH,hp,hx⟩ := hx
  have hB0 : 0 ≤ B := by linarith
  have hp0 : 64 ≤ p 0 := hB.trans hp.1
  have hp1 : 1 ≤ p 1 := by nlinarith only [hp.2.2.1,hB]
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ p 0) hp.2.1 2
  have hba : 48*(p 0)^2 ≤ 25*(p 1) := by nlinarith only [hsq,hp.2.2.1]
  let u := x 0-y 0-p 0
  let v := x 1-y 1-p 1
  have hu : |u| ≤ 5/8 := by
    have hh := abs_sub (x 0-p 0) (y 0)
    have he : (x 0-p 0)-y 0 = u := by dsimp [u]; ring
    rw [he] at hh
    linarith only [hh,hx.1,hy.1]
  have hxl := abs_lt.mp hx.2
  have hyl := abs_lt.mp hy.2
  have hvlo : 15/512 ≤ v := by dsimp [v]; linarith only [hxl.1,hyl.2,hH]
  have hvhi : v ≤ 273/512 := by dsimp [v]; linarith only [hxl.2,hyl.1,hH]
  have hb := retreat_base_sqrt_between (p 1) (p 0) u v hp1 hp0 hba hu hvlo hvhi
  have he : Real.sqrt ((p 1+v)^2+(p 0+u)^2) = dist x y := by
    rw [plane_dist_coordinates]
    dsimp [u,v]
    congr 1
    ring
  rw [he,hpa] at hb
  intro heq
  rw [heq] at hb
  have hlo : a < (m : ℤ) := by exact_mod_cast hb.1
  have hhi : (m : ℤ) < a+1 := by exact_mod_cast hb.2
  omega

theorem retreatInfinity_no_integer :
    ∀ x ∈ retreatInfinity, ∀ y ∈ retreatInfinity, ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ) := by
  intro x hx y hy m hm
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · intro heq
    have hd := retreatBase_diameter hx hy
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hd,heq,hm1]
  · obtain ⟨j,hy⟩ := Set.mem_iUnion.mp hy
    have hh := framed_base_no_integer ((2 : ℝ)^j.val)
      (by have := tail_scale_ge j.val j.property; linarith) (tailGeneration_framed _ _ hy) hx m
    simpa only [dist_comm] using hh
  · obtain ⟨j,hx⟩ := Set.mem_iUnion.mp hx
    exact framed_base_no_integer ((2 : ℝ)^j.val)
      (by have := tail_scale_ge j.val j.property; linarith) (tailGeneration_framed _ _ hx) hy m
  · obtain ⟨j,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i,hy⟩ := Set.mem_iUnion.mp hy
    by_cases hij : i.val = j.val
    · have heq : i = j := Subtype.ext hij
      subst i
      exact retreatRectangles_no_integer _ _ _
        (retreat_parameter_k_ge_eight (tailParameters j.val j.property) j.property)
        _ (tailTrim_spec j.val j.property).2 _ _ x hx y hy m hm
    · rcases lt_or_gt_of_ne hij with hij | hij
      · have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show i.val+1 ≤ j.val by omega)
        rw [pow_succ] at hp
        apply framed_cross_no_integer ((2 : ℝ)^j.val) ((2 : ℝ)^i.val)
          (tail_scale_ge j.val j.property) (by have := tail_scale_ge i.val i.property; linarith)
          (by nlinarith only [hp]) (tailGeneration_framed _ _ hx) (tailGeneration_framed _ _ hy) m
      · have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show j.val+1 ≤ i.val by omega)
        rw [pow_succ] at hp
        have hh := framed_cross_no_integer ((2 : ℝ)^i.val) ((2 : ℝ)^j.val)
          (tail_scale_ge i.val i.property) (by have := tail_scale_ge j.val j.property; linarith)
          (by nlinarith only [hp]) (tailGeneration_framed _ _ hy) (tailGeneration_framed _ _ hx) m
        simpa only [dist_comm] using hh

theorem wideRectangle_isOpen (p : Plane) (H : ℝ) : IsOpen (wideRectangle p H) := by
  have h0 : Continuous (fun x : Plane => x 0) := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous (fun x : Plane => x 1) := PiLp.continuous_apply 2 _ 1
  exact (isOpen_lt (h0.sub continuous_const).abs continuous_const).inter
    (isOpen_lt (h1.sub continuous_const).abs continuous_const)

theorem retreatBase_isOpen : IsOpen retreatBase := by
  have h0 : Continuous (fun x : Plane => x 0) := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous (fun x : Plane => x 1) := PiLp.continuous_apply 2 _ 1
  exact (isOpen_lt h0.abs continuous_const).inter
    (isOpen_lt (h1.add continuous_const).abs continuous_const)

theorem tailGeneration_isOpen (j : ℕ) (hj : 14 ≤ j) : IsOpen (tailGeneration j hj) :=
  isOpen_iUnion (fun _ => wideRectangle_isOpen _ _)

theorem retreatInfinity_isOpen : IsOpen retreatInfinity :=
  retreatBase_isOpen.union (isOpen_iUnion (fun j => tailGeneration_isOpen j.val j.property))

theorem framedRectanglePoint_radius (B : ℝ) (hB : 64 ≤ B) {x : Plane}
    (hx : framedRectanglePoint B x) : dist x 0 < 4*B^2 := by
  obtain ⟨p,a,H,hpa,hH0,hH,hp,hx⟩ := hx
  have hpp : p ∈ wideRectangle p H := by
    constructor
    · simp only [sub_self,abs_zero]; norm_num
    · simp only [sub_self,abs_zero]; positivity
  have hd := wideRectangle_diameter p H hH hx hpp
  have hB0 : 0 ≤ B := by linarith
  have hp0 : 0 ≤ p 0 := hB0.trans hp.1
  have hp1 : 0 ≤ p 1 := (by positivity : 0 ≤ 3*B^2).trans hp.2.2.1
  have hnorm : dist p 0 ≤ p 0+p 1 := by
    rw [plane_dist_coordinates]
    simp only [PiLp.zero_apply,sub_zero]
    have hs := Real.sq_sqrt (show 0 ≤ (p 0)^2+(p 1)^2 by positivity)
    have hs0 := Real.sqrt_nonneg ((p 0)^2+(p 1)^2)
    nlinarith only [hs,hs0,hp0,hp1,mul_nonneg hp0 hp1]
  have htri := dist_triangle x p 0
  nlinarith only [htri,hd,hnorm,hp.2.1,hp.2.2.2,hB]

theorem tailGeneration_subset_ball (j : ℕ) (hj : 14 ≤ j) :
    tailGeneration j hj ⊆ Metric.ball (0 : Plane) (generationRadius j) := by
  intro x hx
  apply Metric.mem_ball.mpr
  have hh := framedRectanglePoint_radius ((2 : ℝ)^j)
    (by have := tail_scale_ge j hj; linarith) (tailGeneration_framed j hj hx)
  have hp : generationRadius j = 4*((2 : ℝ)^j)^2 := by
    have he : (4 : ℝ)^j = ((2 : ℝ)^j)^2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul]
      congr 1
      omega
    unfold generationRadius
    rw [pow_succ,he]
    ring
  simpa only [hp] using hh

theorem tailGeneration_nonempty (j : ℕ) (hj : 14 ≤ j) :
    (tailGeneration j hj).Nonempty := by
  let P := tailParameters j hj
  let t := tailTrim j hj
  have ht := tailTrim_spec j hj
  change 1 ≤ t ∧ 2*t ≤ P.k at ht
  have hq : 0 < P.k-t := by omega
  let α : Fin P.n → Fin (P.k-t) := fun _ => ⟨0,hq⟩
  let p := retreatPoint P.k t P.n ht.1 ((2 : ℤ)^j) (3*((2 : ℤ)^j)^2) α
  refine ⟨p,?_⟩
  change p ∈ retreatRectangles P.k t P.n ht.1 ((2 : ℤ)^j) (3*((2 : ℤ)^j)^2)
  apply Set.mem_iUnion.mpr
  refine ⟨α,?_⟩
  change |p 0-p 0| < 1/4 ∧ |p 1-p 1| < retreatHeight P.k t/2
  constructor
  · simp only [sub_self,abs_zero]; norm_num
  · simp only [sub_self,abs_zero]
    have hH := (retreatHeight_bounds P.k t (retreat_parameter_k_ge_eight P hj) ht.1).1
    positivity

theorem retreatInfinity_unbounded (R : ℝ) :
    ∃ x ∈ retreatInfinity, R < dist x 0 := by
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (max R 0+1) (by norm_num : (1 : ℝ) < 2)
  let j := N+14
  have hj : 14 ≤ j := by omega
  obtain ⟨x,hx⟩ := tailGeneration_nonempty j hj
  obtain ⟨p,a,H,hpa,hH0,hH,hp,hxp⟩ := tailGeneration_framed j hj hx
  have hB := tail_scale_ge j hj
  have hNle : (2 : ℝ)^N ≤ (2 : ℝ)^j :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hRB : R < (2 : ℝ)^j := by
    have hh := le_max_left R 0
    linarith only [hN,hNle,hh]
  have hcoord := abs_lt.mp hxp.2
  have hBx : (2 : ℝ)^j < x 1 := by
    nlinarith only [hB,hp.2.2.1,hcoord.1,hH]
  have hx1 : 0 ≤ x 1 := by linarith only [hB,hBx]
  have hnorm : x 1 ≤ dist x 0 := by
    rw [plane_dist_coordinates]
    simp only [PiLp.zero_apply,sub_zero]
    have hs := Real.sq_sqrt (show 0 ≤ (x 0)^2+(x 1)^2 by positivity)
    have hs0 := Real.sqrt_nonneg ((x 0)^2+(x 1)^2)
    nlinarith only [hs,hs0,hx1,sq_nonneg (x 0)]
  exact ⟨x,Or.inr (Set.mem_iUnion.mpr ⟨⟨j,hj⟩,hx⟩),(hRB.trans hBx).trans_le hnorm⟩

#print axioms retreatInfinity_unbounded
#print axioms tailGeneration_subset_ball
#print axioms retreatInfinity_isOpen
#print axioms retreatInfinity_no_integer
end
end Erdos953Lower
