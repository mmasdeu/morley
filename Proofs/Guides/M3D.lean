/-
  Member m3 (swarm smwh7aexl), direction d5.

  Part D: `guideLines_card` from the two exclusion hypotheses of `M3G`:
  `m3HPnd` (non-diagonal pairs are never side-parallel) gives the constructive lower bound
  `9 ≤ ncard` (M3C2), and `m3HPnd` + `m3DiagExc` (no guide line carries a diagonal pair)
  give `hclass`, hence the root's upper bound `m5_ncard_le_nine`.
-/
import M3C2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set

namespace XamboMorley
namespace OrientedTriangle

open XamboMorley.OrientedTriangle.OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-- **`guideLines_card`** from the two exclusion hypotheses: the number of guide lines of a
triangle with injective constellation is exactly nine.  The root statement
`guideLines_card` verbatim, with `m3HPnd` and `m3DiagExc` as the only extra input. -/
theorem m3_guideLines_card (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) (HD : m3DiagExc T) : T.guideLines.ncard = 9 :=
  le_antisymm (m5_ncard_le_nine T h (m3_hclass_of_exc T HPnd HD))
    (m3_nine_le_ncard T h HPnd)

/-- The upper bound alone. -/
theorem m3_guideLines_ncard_le_nine (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (HPnd : m3HPnd T) (HD : m3DiagExc T) :
    T.guideLines.ncard ≤ 9 :=
  m5_ncard_le_nine T h (m3_hclass_of_exc T HPnd HD)

end OrientedTriangle
end XamboMorley
