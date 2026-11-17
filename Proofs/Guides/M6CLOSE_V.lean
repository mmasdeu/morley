/-
  Member m6, swarm smwhbig2n.  Direction d5 — the point-incidence half of the nine guide
  lines, and now the closing of three of the four root `sorry`s.

  The two halves of the guide-line count are both available unconditionally, from two
  different arguments:

  * **upper bound** `T.guideLines.ncard ≤ 9`
    (`XamboMorley.M6.m6_guideLines_ncard_le_nine`, `.ultramath/smwha0atu/m6/M6Block.lean`):
    pure incidence counting.  Each of the nine equal-sum joins `m4L s d` carries its six
    constellation points, each of the 27 labels lies in exactly two of the nine six-sets,
    and two common points force two canonical lines to coincide.  Hence a guide line which
    is not one of the nine would give `6 · 2 = 12 > 9` distinct eight-index sets.  No
    diagonal-pair exclusion, no Möbius algebra.
  * **lower bound** `9 ≤ T.guideLines.ncard`
    (`m6_nine_le_ncard` below, `.ultramath/smwhbig2n/m6/M6TWO.lean`): the double count
    `6 · ncard = Σ_q #{guide lines through q}` with `#{…} ≥ 2` at every one of the 27
    points (the compiled 54-incidence certificate `m2_two_guide_lines`).

  Then

  * `guideLines_card`            : `ncard = 9`,
  * `point_on_two_guideLines`    : every point is on exactly two guide lines (the `≥ 2`
    side is compiled, so nothing has to bound concurrency from above),
  * `guideLines_direction_card`  : at most three in a direction
    (`XamboMorley.M6.m6_direction_le_three`, also unconditional) and at least the three
    constructed side-parallel lines `m3dirLines`.

  No `sorry`, no `admit`, no new axiom.
-/
import M6BlockV
import M6TWO
import M3E
import M2ND

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

/-- **The root's `guideLines_card`.**  Exactly nine guide lines. -/
theorem m6_guideLines_card (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.guideLines.ncard = 9 :=
  le_antisymm (XamboMorley.M6.m6_guideLines_ncard_le_nine T h) (m6_nine_le_ncard T h)

/-- **The root's `point_on_two_guideLines`.**  Every constellation point is incident with
exactly two guide lines. -/
theorem m6_point_on_two_guideLines (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (q : ConstellationIndex) :
    {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2 :=
  m6_point_on_two_of_ncard_le T h (XamboMorley.M6.m6_guideLines_ncard_le_nine T h) q

/-- **The root's `guideLines_direction_card`.**  Three guide lines in each Morley-side
direction.  Upper bound: `XamboMorley.M6.m6_direction_le_three` (unconditional, for every
vector).  Lower bound: the three constructed lines `m3dirLines T h d` in that direction,
which are guide lines by the compiled non-diagonal exclusions `m2_m3HPnd`. -/
theorem m6_guideLines_direction_card (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (v : E)
    (hv : v = T.Y - T.X ∨ v = T.Z - T.Y ∨ v = T.X - T.Z) :
    {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard = 3 := by
  classical
  refine le_antisymm (XamboMorley.M6.m6_direction_le_three T h v) ?_
  have HPnd : m3HPnd T := m2_m3HPnd T h
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  rcases hv with rfl | rfl | rfl
  · have hsub := m3dirLines_sub T h HPnd (0 : TrisectorLabel)
    rw [m3p_side_zero] at hsub
    calc 3 = (m3dirLines T h 0).ncard := (m3dirLines_ncard T h HPnd 0).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (hfin.subset fun ℓ hℓ => hℓ.1)
  · have hsub := m3dirLines_sub T h HPnd (1 : TrisectorLabel)
    rw [m3p_side_one] at hsub
    calc 3 = (m3dirLines T h 1).ncard := (m3dirLines_ncard T h HPnd 1).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (hfin.subset fun ℓ hℓ => hℓ.1)
  · have hsub := m3dirLines_sub T h HPnd (2 : TrisectorLabel)
    rw [m3p_side_two] at hsub
    calc 3 = (m3dirLines T h 2).ncard := (m3dirLines_ncard T h HPnd 2).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (hfin.subset fun ℓ hℓ => hℓ.1)

/-- The guide-line count from the incidence argument alone, restated for the assembly: the
upper bound and the lower bound can also be combined without the `≥ 2` certificate. -/
theorem m6_guideLines_card' (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.guideLines.ncard = 9 :=
  le_antisymm (XamboMorley.M6.m6_guideLines_ncard_le_nine T h) (m2_nine_le_ncard T h)

end OrientedTriangle
end XamboMorley
