/-
  member m2, swarm smwha0atu, direction d8: the consequences of the unconditional
  non-diagonal exclusion family `m2_m3HPnd` (in `M2ND.lean`).

  Everything here that does not mention `m3DiagExc` is UNCONDITIONAL (for every
  nondegenerate oriented triangle with injective constellation):

  * `m2_nine_le_ncard`      : `9 ≤ T.guideLines.ncard`  (constructive lower bound;
                              the `≥` half of `guideLines_card`);
  * `m2_no_third_nd`        : no side-parallel line carries a *third* same-colour
                              point when two of them form an equal-sum non-diagonal pair
                              ("bare-line exactness");
  * `m2_colour_two_nd`      : hence exactly two points of that colour lie on it.

  The two remaining `guideLines` principals then need only `T.m3DiagExc` — the diagonal
  exclusion hypothesis, which is exactly the `no_diag` shape of `m5/M5B.lean` and is the
  object of the per-pair diagonals directions (d2, d3, d4, d5, d7):

  * `m2_hclass`                   : the root's `hclass`;
  * `m2_guideLines_card`          : `T.guideLines.ncard = 9`;
  * `m2_guideLines_direction_card`: three guide lines in each Morley direction.
-/
import M2ND
import M3D
import M3E

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

/-- **The constructive lower bound, unconditionally**: a triangle with injective
constellation has at least nine guide lines. -/
theorem m2_nine_le_ncard (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    9 ≤ T.guideLines.ncard :=
  m3_nine_le_ncard T h (m2_m3HPnd T h)

/-- **No third point of a colour on a side-parallel line** (bare-line exactness), from the
non-diagonal family only. -/
theorem m2_no_third_nd (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {ℓ : Line E} (hdir : T.parallelToMorleySide ℓ.direction)
    {cc : TrisectorColor} {p1 p2 r : TrisectorLabel × TrisectorLabel}
    (hne : p1 ≠ p2) (hnd : ¬ m3Diag p1 p2) (hsame : p1.1 + p1.2 = p2.1 + p2.2)
    (hm1 : ℓ.mem (T.constellationPoint ⟨cc, p1.1, p1.2⟩))
    (hm2 : ℓ.mem (T.constellationPoint ⟨cc, p2.1, p2.2⟩))
    (hr : ℓ.mem (T.constellationPoint ⟨cc, r.1, r.2⟩))
    (hr1 : r ≠ p1) (hr2 : r ≠ p2) : False :=
  m3_no_third_nd T h (m2_m3HPnd T h) hdir hne hnd hsame hm1 hm2 hr hr1 hr2

/-- **Exactly two points of a colour on a side-parallel line**, from the non-diagonal
family only. -/
theorem m2_colour_two_nd (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {ℓ : Line E} (hdir : T.parallelToMorleySide ℓ.direction)
    {cc : TrisectorColor} {p1 p2 : TrisectorLabel × TrisectorLabel}
    (hne : p1 ≠ p2) (hnd : ¬ m3Diag p1 p2) (hsame : p1.1 + p1.2 = p2.1 + p2.2)
    (hm1 : ℓ.mem (T.constellationPoint ⟨cc, p1.1, p1.2⟩))
    (hm2 : ℓ.mem (T.constellationPoint ⟨cc, p2.1, p2.2⟩)) :
    {q : ConstellationIndex | q.color = cc ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2 :=
  m3_colour_two_nd T h (m2_m3HPnd T h) hdir hne hnd hsame hm1 hm2

/-- The root's `hclass` from the non-diagonal family and the diagonal exclusion. -/
theorem m2_hclass (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HD : m3DiagExc T) :
    ∀ (ℓ : Line E), ℓ ∈ T.guideLines → ∀ p q : TrisectorLabel × TrisectorLabel,
      ℓ.mem (T.m5_redPt p) → ℓ.mem (T.m5_redPt q) → p.1 + p.2 = q.1 + q.2 :=
  m3_hclass_of_exc T (m2_m3HPnd T h) HD

/-- **`guideLines_card`** with the diagonal exclusions as the only remaining input. -/
theorem m2_guideLines_card (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HD : m3DiagExc T) : T.guideLines.ncard = 9 :=
  m3_guideLines_card T h (m2_m3HPnd T h) HD

/-- **`guideLines_direction_card`** with the diagonal exclusions as the only remaining
input. -/
theorem m2_guideLines_direction_card (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (HD : m3DiagExc T) (v : E)
    (hv : v = T.Y - T.X ∨ v = T.Z - T.Y ∨ v = T.X - T.Z) :
    {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard = 3 :=
  m3_guideLines_direction_card T h (m2_m3HPnd T h) HD v hv

/-- The upper bound on its own. -/
theorem m2_guideLines_ncard_le_nine (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (HD : m3DiagExc T) :
    T.guideLines.ncard ≤ 9 :=
  m3_guideLines_ncard_le_nine T h (m2_m3HPnd T h) HD

end OrientedTriangle
end XamboMorley

#print axioms XamboMorley.OrientedTriangle.m2_sin_third_add_ne
#print axioms XamboMorley.OrientedTriangle.m2_rot_bStar
#print axioms XamboMorley.OrientedTriangle.m2_side1_rot
#print axioms XamboMorley.OrientedTriangle.m2_redB_not_par
#print axioms XamboMorley.OrientedTriangle.m2_redC_not_par
#print axioms XamboMorley.OrientedTriangle.m2_greenC_not_par
#print axioms XamboMorley.OrientedTriangle.m2_greenA_not_par
#print axioms XamboMorley.OrientedTriangle.m2_blueA_not_par
#print axioms XamboMorley.OrientedTriangle.m2_blueB_not_par
#print axioms XamboMorley.OrientedTriangle.m2_pair_row_or_col
#print axioms XamboMorley.OrientedTriangle.m2_m3HPnd
#print axioms XamboMorley.OrientedTriangle.m2_nine_le_ncard
#print axioms XamboMorley.OrientedTriangle.m2_no_third_nd
#print axioms XamboMorley.OrientedTriangle.m2_colour_two_nd
#print axioms XamboMorley.OrientedTriangle.m2_hclass
#print axioms XamboMorley.OrientedTriangle.m2_guideLines_card
#print axioms XamboMorley.OrientedTriangle.m2_guideLines_direction_card
#print axioms XamboMorley.OrientedTriangle.m2_guideLines_ncard_le_nine
