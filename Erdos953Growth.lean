import Erdos953Sandwich
import Erdos953SharpLower
import Erdos953Retreat
import Erdos953Lower.GrowthRate
import Erdos953Lower.Extremal

/-!
The bounds in `Erdos953Sandwich` determine the logarithmic growth exponent
of the original open-disk extremal area. The upper-bound formalization is due
to Allen Hart and is included in the local project only as an attributed
reference. The abstract limit argument is in the independent lower project.
-/

noncomputable section

open Filter
open scoped Topology

namespace Erdos953Sandwich

/-- The standalone extremal definition is definitionally the same as the
attributed upper-bound project's open-disk formulation. -/
theorem standalone_Mopen_eq_reference (R : ℝ) :
    Erdos953Lower.Mopen R = Erdos953OpenClosed.Mopen R := by
  rfl

/-- The maximal admissible area in an open disk has growth exponent `1/2`.
Equivalently, in standard asymptotic notation, `Mopen(R) = R^(1/2 + o(1))`.
This does not assert `Mopen(R) = Θ(√R)` or an exact value at each radius. -/
theorem growth_exponent_open :
    Tendsto (fun R : ℝ =>
      Real.log (Erdos953OpenClosed.Mopen R) / Real.log R)
      atTop (𝓝 (1 / 2 : ℝ)) :=
  Erdos953Lower.log_growth_exponent_of_bounds
    Erdos953OpenClosed.Mopen growth_sandwich_open.1 growth_sandwich_open.2

#print axioms growth_exponent_open
#print axioms standalone_Mopen_eq_reference

end Erdos953Sandwich
