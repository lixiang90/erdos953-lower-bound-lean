import Erdos953Lower.RetreatDigits
import Erdos953Lower.RetreatGain

namespace Erdos953Lower
open Finset MeasureTheory
noncomputable section
set_option maxHeartbeats 600000

def trimEmbed (k t n : ℕ) (ht : 1 ≤ t) (α : Fin n → Fin (k-t)) :
    Fin n → Fin (k-1) := fun i => ⟨(α i).val, by have := (α i).isLt; omega⟩

theorem trimEmbed_injective (k t n : ℕ) (ht : 1 ≤ t) :
    Function.Injective (trimEmbed k t n ht) := by
  intro α β heq
  funext i
  apply Fin.ext
  have hh := congrArg (fun f => (f i).val) heq
  exact hh

def compressedY (k n : ℕ) (α : Fin n → Fin (k-1)) : ℤ :=
  (k : ℤ)*∑ j ∈ range n, digitAt k n α j * ((k : ℤ)^2)^j

theorem yCoord_compressedY (k n : ℕ) (α : Fin n → Fin (k-1)) :
    yCoord k n α = 8*compressedY k n α := by
  unfold yCoord compressedY
  ring

theorem compressedY_sub (k n : ℕ) (α β : Fin n → Fin (k-1)) :
    compressedY k n α-compressedY k n β =
      (k : ℤ)*∑ j ∈ range n, digitDiff k n α β j*((k : ℤ)^2)^j := by
  unfold compressedY
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  simp [digitDiff, sub_mul]

def retreatPoint (k t n : ℕ) (ht : 1 ≤ t) (bx by₀ : ℤ)
    (α : Fin n → Fin (k-t)) : Plane :=
  !₂[((bx+xCoord k n (trimEmbed k t n ht α) : ℤ) : ℝ),
    ((by₀+compressedY k n (trimEmbed k t n ht α) : ℤ) : ℝ)]

@[simp] theorem retreatPoint_zero (k t n : ℕ) (ht : 1 ≤ t) (bx by₀ : ℤ)
    (α : Fin n → Fin (k-t)) : retreatPoint k t n ht bx by₀ α 0 =
      (bx+xCoord k n (trimEmbed k t n ht α) : ℤ) := by simp [retreatPoint]
@[simp] theorem retreatPoint_one (k t n : ℕ) (ht : 1 ≤ t) (bx by₀ : ℤ)
    (α : Fin n → Fin (k-t)) : retreatPoint k t n ht bx by₀ α 1 =
      (by₀+compressedY k n (trimEmbed k t n ht α) : ℤ) := by simp [retreatPoint]

def retreatRectangles (k t n : ℕ) (ht : 1 ≤ t) (bx by₀ : ℤ) : Set Plane :=
  ⋃ α : Fin n → Fin (k-t),
    wideRectangle (retreatPoint k t n ht bx by₀ α) (retreatHeight k t)

theorem trimmed_digitDiff_bound (k t n : ℕ) (ht : 1 ≤ t) (htk : 2*t ≤ k)
    (α β : Fin n → Fin (k-t)) (j : ℕ) (hj : j < n) :
    |digitDiff k n (trimEmbed k t n ht α) (trimEmbed k t n ht β) j| ≤
      (k : ℤ)-t-1 := by
  have hu := (α ⟨j,hj⟩).isLt
  have hv := (β ⟨j,hj⟩).isLt
  simp only [digitDiff, digitAt, hj, dite_true, trimEmbed]
  rw [abs_le]
  constructor <;> omega

theorem retreatPoint_square_bounds (k t n : ℕ) (hk : 8 ≤ k)
    (ht : 1 ≤ t) (htk : 2*t ≤ k) (bx by₀ : ℤ)
    (α β : Fin n → Fin (k-t)) (hab : α ≠ β) :
    let a : ℝ := |retreatPoint k t n ht bx by₀ α 1-retreatPoint k t n ht bx by₀ β 1|
    let b : ℝ := |retreatPoint k t n ht bx by₀ α 0-retreatPoint k t n ht bx by₀ β 0|
    1 ≤ a ∧ 1 ≤ b ∧ 2*a*retreatHeight k t < (b-1/2)^2 ∧
      (b+1/2)^2 ≤ (45/32 : ℝ)*a := by
  let α' := trimEmbed k t n ht α
  let β' := trimEmbed k t n ht β
  have hab' : α' ≠ β' := (trimEmbed_injective k t n ht).ne hab
  obtain ⟨i,hi,hdi,hzero,_⟩ := exists_highest_digit_difference k n (by omega) α' β' hab'
  have hbound : ∀ j ≤ i, |digitDiff k n α' β' j| ≤ (k : ℤ)-t-1 := by
    intro j hj
    exact trimmed_digitDiff_bound k t n ht htk α β j (hj.trans_lt hi)
  have hh := trimmed_rectangle_bounds k t i (digitDiff k n α' β') hk ht htk hbound hdi
  have hx : xCoord k n α'-xCoord k n β' =
      ∑ j ∈ range (i+1), digitDiff k n α' β' j*(k : ℤ)^j := by
    rw [xCoord_sub]
    exact digitDiff_sum_truncate k n i α' β' hi hzero (k : ℤ)
  have hy : compressedY k n α'-compressedY k n β' =
      (k : ℤ)*∑ j ∈ range (i+1), digitDiff k n α' β' j*((k : ℤ)^2)^j := by
    rw [compressedY_sub, digitDiff_sum_truncate k n i α' β' hi hzero]
  simp only [retreatPoint_zero, retreatPoint_one, Int.cast_add] at ⊢
  have hxx : ((bx : ℝ)+(xCoord k n α' : ℤ))-((bx : ℝ)+(xCoord k n β' : ℤ)) =
      (xCoord k n α'-xCoord k n β' : ℤ) := by push_cast; ring
  have hyy : ((by₀ : ℝ)+(compressedY k n α' : ℤ))-((by₀ : ℝ)+(compressedY k n β' : ℤ)) =
      (compressedY k n α'-compressedY k n β' : ℤ) := by push_cast; ring
  change 1 ≤ |((by₀ : ℝ)+(compressedY k n α' : ℤ))-((by₀ : ℝ)+(compressedY k n β' : ℤ))| ∧
    1 ≤ |((bx : ℝ)+(xCoord k n α' : ℤ))-((bx : ℝ)+(xCoord k n β' : ℤ))| ∧ _
  rw [hxx,hyy,hx,hy,Int.cast_mul,Int.cast_natCast,abs_mul,
    abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  simpa only [Int.cast_abs] using hh

theorem retreatRectangle_cross_between (k t n : ℕ) (hk : 8 ≤ k)
    (ht : 1 ≤ t) (htk : 2*t ≤ k) (bx by₀ : ℤ)
    (α β : Fin n → Fin (k-t)) (hab : α ≠ β) {x y : Plane}
    (hx : x ∈ wideRectangle (retreatPoint k t n ht bx by₀ α) (retreatHeight k t))
    (hy : y ∈ wideRectangle (retreatPoint k t n ht bx by₀ β) (retreatHeight k t)) :
    let a : ℤ := |compressedY k n (trimEmbed k t n ht α)-compressedY k n (trimEmbed k t n ht β)|
    (a : ℝ) < dist x y ∧ dist x y < (a : ℝ)+1 := by
  let p := retreatPoint k t n ht bx by₀ α
  let q := retreatPoint k t n ht bx by₀ β
  let a : ℝ := |p 1-q 1|
  let b : ℝ := |p 0-q 0|
  have hs := retreatPoint_square_bounds k t n hk ht htk bx by₀ α β hab
  change 1 ≤ a ∧ 1 ≤ b ∧ 2*a*retreatHeight k t < (b-1/2)^2 ∧
    (b+1/2)^2 ≤ (45/32 : ℝ)*a at hs
  let u := |x 0-y 0|-b
  let v := |x 1-y 1|-a
  have hu : |u| ≤ 1/2 := by
    have hh := coordinate_perturbation _ _ _ _ _ hx.1 hy.1
    change abs (|x 0-y 0|-b) < 2*(1/4) at hh
    dsimp [u]; linarith only [hh]
  have hv : |v| ≤ retreatHeight k t := by
    have hh := coordinate_perturbation _ _ _ _ _ hx.2 hy.2
    change abs (|x 1-y 1|-a) < 2*(retreatHeight k t/2) at hh
    dsimp [v]; linarith only [hh]
  have hb := retreatHeight_bounds k t hk ht
  have hh := retreat_sqrt_between a b (retreatHeight k t) u v hs.1 hs.2.1
    hb.1.le hb.2.1 hs.2.2.1 hs.2.2.2 hu hv
  have he : Real.sqrt ((a+v)^2+(b+u)^2) = dist x y := by
    rw [plane_dist_coordinates]
    dsimp [u,v]
    congr 1
    simp only [add_sub_cancel,sq_abs]
    ring
  rw [he] at hh
  have ha : a = (|compressedY k n (trimEmbed k t n ht α)-compressedY k n (trimEmbed k t n ht β)| : ℤ) := by
    dsimp [a,p,q]
    simp only [retreatPoint_one,Int.cast_add,Int.cast_abs,Int.cast_sub]
    congr 1
    ring
  simpa only [ha] using hh

theorem retreatRectangles_no_integer (k t n : ℕ) (hk : 8 ≤ k)
    (ht : 1 ≤ t) (htk : 2*t ≤ k) (bx by₀ : ℤ) :
    ∀ x ∈ retreatRectangles k t n ht bx by₀, ∀ y ∈ retreatRectangles k t n ht bx by₀,
      ∀ m : ℕ, 0 < m → dist x y ≠ (m : ℝ) := by
  intro x hx y hy m hm heq
  obtain ⟨α,hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨β,hy⟩ := Set.mem_iUnion.mp hy
  by_cases hab : α = β
  · subst β
    have hh := wideRectangle_diameter _ _ (retreatHeight_bounds k t hk ht).2.1 hx hy
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hh,hm1,heq]
  · have hh := retreatRectangle_cross_between k t n hk ht htk bx by₀ α β hab hx hy
    rw [heq] at hh
    have hlo : |compressedY k n (trimEmbed k t n ht α)-compressedY k n (trimEmbed k t n ht β)| < (m : ℤ) := by
      exact_mod_cast hh.1
    have hhi : (m : ℤ) < |compressedY k n (trimEmbed k t n ht α)-compressedY k n (trimEmbed k t n ht β)|+1 := by
      exact_mod_cast hh.2
    omega

theorem retreatRectangles_measurable (k t n : ℕ) (ht : 1 ≤ t) (bx by₀ : ℤ) :
    MeasurableSet (retreatRectangles k t n ht bx by₀) :=
  MeasurableSet.iUnion (fun _ => wideRectangle_measurable _ _)

theorem retreatRectangles_disjoint (k t n : ℕ) (hk : 8 ≤ k)
    (ht : 1 ≤ t) (htk : 2*t ≤ k) (bx by₀ : ℤ) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin n → Fin (k-t)))
      (fun α => wideRectangle (retreatPoint k t n ht bx by₀ α) (retreatHeight k t)) := by
  intro α _ β _ hab
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := coordinate_perturbation (x 0) (x 0) _ _ (1/4) hx.1 hy.1
  have hrat := (retreatPoint_square_bounds k t n hk ht htk bx by₀ α β hab).2.1
  simp only [sub_self,abs_zero,zero_sub,abs_neg,abs_abs] at hh
  linarith only [hh,hrat]

theorem retreatRectangles_volume (k t n : ℕ) (hk : 8 ≤ k)
    (ht : 1 ≤ t) (htk : 2*t ≤ k) (bx by₀ : ℤ) :
    volume (retreatRectangles k t n ht bx by₀) = ENNReal.ofReal (retreatArea k n t) := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n → Fin (k-t))))
      (fun α => wideRectangle (retreatPoint k t n ht bx by₀ α) (retreatHeight k t)) := by
    simpa only [Finset.coe_univ] using retreatRectangles_disjoint k t n hk ht htk bx by₀
  have hv := measure_biUnion_finset (μ := volume) hd (fun _ _ => wideRectangle_measurable _ _)
  have hv' : volume (retreatRectangles k t n ht bx by₀) =
      (((k-t)^n : ℕ) : ENNReal)*ENNReal.ofReal (retreatHeight k t/2) := by
    simpa [retreatRectangles,wideRectangle_volume,Fintype.card_fun] using hv
  rw [hv',← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg ((k-t)^n))]
  congr 1
  rw [Nat.cast_pow,Nat.cast_sub (by omega : t ≤ k)]
  unfold retreatArea
  ring

#print axioms retreatRectangles_no_integer
#print axioms retreatRectangles_volume
end
end Erdos953Lower
