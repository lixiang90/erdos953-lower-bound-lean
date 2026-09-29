/-
  Erdős Problem 953: elementary distance gap for the lower construction.
  The nearest-integer argument is adapted from Erdos466.lean in
  plby/lean-proofs (Apache 2.0, commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e).
  The inequality itself is the elementary square-root estimate used by
  Sárközy and in Goenka--Moore, arXiv:2605.06621, Lemma 3.1.
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Erdos953Lower

noncomputable section

/-- Distance from a real number to the nearest integer. -/
def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma distToInt_gt_of_between {x δ : ℝ} (a : ℤ)
    (hleft : (a : ℝ) + δ < x)
    (hright : x < (a : ℝ) + 1 - δ) :
    δ < distToInt x := by
  rw [distToInt]
  let z : ℤ := round x
  have hz : z ≤ a ∨ a + 1 ≤ z := by omega
  rcases hz with hza | haz
  · have hza' : (z : ℝ) ≤ (a : ℝ) := by exact_mod_cast hza
    calc
      δ < x - (z : ℝ) := by linarith
      _ ≤ |x - (z : ℝ)| := le_abs_self _
  · have haz' : (a : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast haz
    calc
      δ < -(x - (z : ℝ)) := by linarith
      _ ≤ |x - (z : ℝ)| := neg_le_abs _

/-- If the nonintegral squared-distance contribution is proportional to a
positive integral coordinate difference, the Euclidean distance stays away
from every integer. The generous constants suit the digit construction. -/
theorem sqrt_sq_add_away (a : ℤ) (r δ : ℝ)
    (ha : 1 ≤ a) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4)
    (hlo : 3 * δ * (a : ℝ) ≤ r)
    (hhi : r ≤ (a : ℝ)) :
    δ < distToInt (Real.sqrt ((a : ℝ) ^ 2 + r)) := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hr : 0 ≤ r := by nlinarith
  have hbase : 0 ≤ (a : ℝ) ^ 2 + r := by positivity
  have hs0 : 0 ≤ Real.sqrt ((a : ℝ) ^ 2 + r) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt ((a : ℝ) ^ 2 + r) ^ 2 = (a : ℝ) ^ 2 + r :=
    Real.sq_sqrt hbase
  apply distToInt_gt_of_between a
  · nlinarith [mul_nonneg (show 0 ≤ δ by linarith) (show 0 ≤ (a : ℝ) - δ by linarith)]
  · nlinarith

#print axioms sqrt_sq_add_away

end

end Erdos953Lower
