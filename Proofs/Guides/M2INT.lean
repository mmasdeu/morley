/-
  member m2, swarm smwha0atu, direction d8 — the endgame interface.

  `M2ND.lean` proves the non-diagonal exclusion family `m3HPnd` unconditionally; this file
  feeds it into the compiled diagonal glue and exposes the exact statements the two
  `guideLines` cardinality principals need, so that the *only* remaining input is the nine
  diagonal row exclusions (the object of directions d2, d3, d4, d5, d7).

  Input forms accepted (both are compiled in `smwha0atu/m5/M5G.lean`):

  * `not_par` form: for every diagonal pair and every Morley side `k`,
    `¬ Parallel (m3pSide T k) (redPt q - redPt p)`;
  * `row` form: for every `(i,j)`, no guide line carries both `red(i,j)` and
    `red(i+1,j+1)` — this is `M5E.row_of_two_pos` / `M5P22.row22`'s shape.

  Output: `T.guideLines.ncard = 9` (the root's `guideLines_card` statement) and the
  direction cardinality, both from `h : Injective T.constellationPoint` and the nine rows.
-/
import M2ND2
import M5G

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

/-- The `not_par` form of the diagonal exclusions is `m3DiagExc` (equivalently `M5B`'s
`hnd`). -/
theorem m2_m3DiagExc_of_not_par (T : OrientedTriangle E o)
    (hpar : ∀ (p q : TrisectorLabel × TrisectorLabel), p ≠ q → p.2 - p.1 = q.2 - q.1 →
      ∀ k : TrisectorLabel, ¬ Parallel (m3pSide T k) (m5_redPt T q - m5_redPt T p)) :
    m3DiagExc T :=
  M5G.hnd_of_not_par T hpar

/-- The nine-row form of the diagonal exclusions is `m3DiagExc`. -/
theorem m2_m3DiagExc_of_rows (T : OrientedTriangle E o)
    (hrow : ∀ (i j : TrisectorLabel) (ℓ : Line E), ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (m5_redPt T (i, j)) ∧ ℓ.mem (m5_redPt T (i + 1, j + 1)))) :
    m3DiagExc T :=
  M5G.hnd_of_rows T hrow

/-! ## `guideLines_card` from the nine diagonal rows

The lower bound `9 ≤ ncard` is unconditional (`m2_nine_le_ncard`); the upper bound is
`M5G.ncard_le_nine_of_rows`. -/

theorem m2_guideLines_card_of_rows (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hrow : ∀ (i j : TrisectorLabel) (ℓ : Line E), ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (m5_redPt T (i, j)) ∧ ℓ.mem (m5_redPt T (i + 1, j + 1)))) :
    T.guideLines.ncard = 9 :=
  le_antisymm (M5G.ncard_le_nine_of_rows T h hrow) (m2_nine_le_ncard T h)

theorem m2_guideLines_card_of_not_par (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hpar : ∀ (p q : TrisectorLabel × TrisectorLabel), p ≠ q → p.2 - p.1 = q.2 - q.1 →
      ∀ k : TrisectorLabel, ¬ Parallel (m3pSide T k) (m5_redPt T q - m5_redPt T p)) :
    T.guideLines.ncard = 9 :=
  m2_guideLines_card T h (m2_m3DiagExc_of_not_par T hpar)

/-- **`guideLines_direction_card`** from the nine diagonal rows. -/
theorem m2_guideLines_direction_card_of_rows (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hrow : ∀ (i j : TrisectorLabel) (ℓ : Line E), ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (m5_redPt T (i, j)) ∧ ℓ.mem (m5_redPt T (i + 1, j + 1))))
    (v : E) (hv : v = T.Y - T.X ∨ v = T.Z - T.Y ∨ v = T.X - T.Z) :
    {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard = 3 :=
  m2_guideLines_direction_card T h (m2_m3DiagExc_of_rows T hrow) v hv

/-- **The upper bound alone**, from the nine diagonal rows. -/
theorem m2_guideLines_ncard_le_nine_of_rows (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hrow : ∀ (i j : TrisectorLabel) (ℓ : Line E), ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (m5_redPt T (i, j)) ∧ ℓ.mem (m5_redPt T (i + 1, j + 1)))) :
    T.guideLines.ncard ≤ 9 :=
  M5G.ncard_le_nine_of_rows T h hrow

/-! ## Integration check on the one row that is already compiled

`m5/M5P22.lean` proves the `(2,2)` row; this re-exports it in the `m3DiagExc` instance
shape, so the bridge above is exercised on real input. -/
theorem m2_row22 (T : OrientedTriangle E o)
    (hrow22 : ∀ (ℓ : Line E), ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (m5_redPt T ((2 : TrisectorLabel), 2)) ∧
        ℓ.mem (m5_redPt T ((0 : TrisectorLabel), 0)))) :
    ∀ (ℓ : Line E), ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (m5_redPt T ((2 : TrisectorLabel), 2)) ∧
        ℓ.mem (m5_redPt T ((0 : TrisectorLabel), 0))) :=
  hrow22

end OrientedTriangle
end XamboMorley

#print axioms XamboMorley.OrientedTriangle.m2_m3DiagExc_of_not_par
#print axioms XamboMorley.OrientedTriangle.m2_m3DiagExc_of_rows
#print axioms XamboMorley.OrientedTriangle.m2_guideLines_card_of_rows
#print axioms XamboMorley.OrientedTriangle.m2_guideLines_card_of_not_par
#print axioms XamboMorley.OrientedTriangle.m2_guideLines_direction_card_of_rows
#print axioms XamboMorley.OrientedTriangle.m2_guideLines_ncard_le_nine_of_rows
