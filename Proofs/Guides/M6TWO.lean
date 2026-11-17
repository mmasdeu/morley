/-
  Member m6, swarm smwhbig2n.  Direction d5: POINT_ON_TWO_GUIDELINES_FROM_SCRATCH.

  The root's `point_on_two_guideLines` says *exactly* two guide lines pass through every
  constellation point.  The route used by the root's own `m4_*` block needs the upper
  bound `ncard ≤ 2` on that number (i.e. no three concurrent guide lines), which is the
  expensive side.  The route here needs no concurrency statement at all: it combines

  * `m2_two_guide_lines` (`.ultramath/smwha0atu/m2/M2PTS.lean`): every constellation point
    lies on **at least** two guide lines (this is the compiled 54-incidence certificate,
    `m3LA0 … m3LC0`), and
  * the upper bound `T.guideLines.ncard ≤ 9`, which the diagonal exclusions supply
    (`m3_guideLines_ncard_le_nine` of `.ultramath/smwh7aexl/m3/M3D.lean`),

  through the double count

      6 · ncard(guideLines) = Σ_ℓ #{q : ℓ ∋ q} = Σ_q #{ℓ : ℓ ∋ q} ≥ 27 · 2 = 54.

  The left side is `≤ 54` as soon as `ncard ≤ 9`, and the right side is `≥ 54`, so the
  totals are equal and every summand of the right side is exactly two.  Equivalently, the
  count `≥ 2` *is* the exact count once the number of lines is known.

  Also proved here: the lower bound `9 ≤ ncard` from the same double count (no
  `m3HPnd` needed), and hence `guideLines_card` from the upper bound alone.

  Everything is unconditional apart from the stated counting hypothesis `ncard ≤ 9`;
  no `sorry`, no `admit`, no new axiom.
-/
import M3D
import M2INT
import M2PTS

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

/-! ### Every constellation point lies on at least two guide lines -/

/-- `m2_two_guide_lines` in `Finset` form: at least two guide lines pass through `q`. -/
theorem m6_two_le_linesOn (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (q : ConstellationIndex) :
    2 ≤ (m4_linesOn T (m4_guideLines_finite T h) q).card := by
  classical
  obtain ⟨ℓ₁, hℓ₁, ℓ₂, hℓ₂, hne, hm₁, hm₂⟩ := m2_two_guide_lines T h q
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have hmem₁ : ℓ₁ ∈ hfin.toFinset.filter (fun ℓ : Line E => ℓ.mem (T.constellationPoint q)) := by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hℓ₁, hm₁⟩
  have hmem₂ : ℓ₂ ∈ hfin.toFinset.filter (fun ℓ : Line E => ℓ.mem (T.constellationPoint q)) := by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hℓ₂, hm₂⟩
  have hlt : 1 < (hfin.toFinset.filter (fun ℓ : Line E => ℓ.mem (T.constellationPoint q))).card :=
    Finset.one_lt_card.mpr ⟨ℓ₁, hmem₁, ℓ₂, hmem₂, hne⟩
  have h2 : 2 ≤ (hfin.toFinset.filter (fun ℓ : Line E => ℓ.mem (T.constellationPoint q))).card :=
    hlt
  simpa only [m4_linesOn] using h2

/-- The same bound in `Set.ncard` form, which is the shape of the root statement. -/
theorem m6_two_le_ncard (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (q : ConstellationIndex) :
    2 ≤ {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  rw [m4_ncard_sep (fun ℓ : Line E => ℓ.mem (T.constellationPoint q)) hfin]
  exact m6_two_le_linesOn T h q

/-! ### The double count, in the two directions it is used -/

/-- The total incidence count, written over the lines: `6 · ncard(guideLines)`. -/
theorem m6_sum_lines (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Finset.sum (m4_guideLines_finite T h).toFinset (fun ℓ => (m4_ptsOn T ℓ).card)
      = (m4_guideLines_finite T h).toFinset.card * 6 := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  rw [Finset.sum_congr rfl (fun ℓ hℓ => m4_ptsOn_card_of_mem T (hfin.mem_toFinset.mp hℓ)),
    Finset.sum_const, smul_eq_mul]

/-- The total incidence count, written over the points, is at least `27 · 2`. -/
theorem m6_sum_points_ge (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    27 * 2 ≤ Finset.sum Finset.univ
      (fun q : ConstellationIndex => (m4_linesOn T (m4_guideLines_finite T h) q).card) := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have hcard27 : Fintype.card ConstellationIndex = 27 := by decide
  have h1 : Finset.sum Finset.univ (fun _ : ConstellationIndex => 2)
      ≤ Finset.sum Finset.univ
        (fun q : ConstellationIndex => (m4_linesOn T hfin q).card) :=
    Finset.sum_le_sum (fun q _ => m6_two_le_linesOn T h q)
  have h2 : Finset.sum Finset.univ (fun _ : ConstellationIndex => 2) = 27 * 2 := by
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, hcard27]
  omega

/-- **The lower bound `9 ≤ ncard`** from the point-side count alone (no `m3HPnd`). -/
theorem m6_nine_le_ncard (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    9 ≤ T.guideLines.ncard := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have hsum := m4_double_count T hfin
  have hL := m6_sum_lines T h
  have hR := m6_sum_points_ge T h
  have hcard : T.guideLines.ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  rw [hcard]
  omega

/-- **`guideLines_card` from the upper bound alone.**  The lower bound is the double count
above, so `ncard ≤ 9` already forces the exact number. -/
theorem m6_guideLines_card_of_le (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (h9 : T.guideLines.ncard ≤ 9) : T.guideLines.ncard = 9 :=
  le_antisymm h9 (m6_nine_le_ncard T h)

/-! ### The root statement -/

/-- **`point_on_two_guideLines` from `ncard ≤ 9`.**  Every constellation point lies on
exactly two guide lines: the totals `6 · ncard ≤ 54` and `Σ_q #{ℓ} ≥ 27 · 2 = 54` agree, so
each of the 27 summands, already `≥ 2`, is exactly two. -/
theorem m6_point_on_two_of_ncard_le (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (h9 : T.guideLines.ncard ≤ 9) :
    ∀ q : ConstellationIndex,
      {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2 := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have hcard27 : Fintype.card ConstellationIndex = 27 := by decide
  have hcard9 : hfin.toFinset.card ≤ 9 := by
    rw [Set.ncard_eq_toFinset_card _ hfin] at h9
    exact h9
  have hL : Finset.sum hfin.toFinset (fun ℓ => (m4_ptsOn T ℓ).card) ≤ 54 := by
    rw [m6_sum_lines T h]
    omega
  have hR : 27 * 2 ≤ Finset.sum Finset.univ
      (fun q : ConstellationIndex => (m4_linesOn T hfin q).card) := m6_sum_points_ge T h
  have h54 : Finset.sum Finset.univ
      (fun q : ConstellationIndex => (m4_linesOn T hfin q).card) = 54 := by
    have hd := m4_double_count T hfin
    omega
  intro q
  have hsplit : Finset.sum Finset.univ (fun q : ConstellationIndex => (m4_linesOn T hfin q).card)
      = (m4_linesOn T hfin q).card +
        Finset.sum (Finset.univ.erase q)
          (fun x : ConstellationIndex => (m4_linesOn T hfin x).card) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ q)).symm
  have hrest_ge : 52 ≤ Finset.sum (Finset.univ.erase q)
      (fun x : ConstellationIndex => (m4_linesOn T hfin x).card) := by
    have h1 : Finset.sum (Finset.univ.erase q) (fun _ : ConstellationIndex => 2)
        ≤ Finset.sum (Finset.univ.erase q)
          (fun x : ConstellationIndex => (m4_linesOn T hfin x).card) :=
      Finset.sum_le_sum (fun x _ => m6_two_le_linesOn T h x)
    have h2 : Finset.sum (Finset.univ.erase q) (fun _ : ConstellationIndex => 2) = 52 := by
      rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ q),
        Finset.card_univ, hcard27]
    omega
  have hq_ge : 2 ≤ (m4_linesOn T hfin q).card := m6_two_le_linesOn T h q
  have hq2 : (m4_linesOn T hfin q).card = 2 := by omega
  rw [m4_ncard_sep (fun ℓ : Line E => ℓ.mem (T.constellationPoint q)) hfin]
  exact hq2

/-- The root statement from the exact line count. -/
theorem m6_point_on_two_of_ncard_eq (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (hcard : T.guideLines.ncard = 9) :
    ∀ q : ConstellationIndex,
      {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2 :=
  m6_point_on_two_of_ncard_le T h (le_of_eq hcard)

/-- **The root statement from the diagonal exclusions**: `m3HPnd` (the compiled non-diagonal
exclusions of `M2ND`) together with `m3DiagExc` (the nine diagonal-pair exclusions) give the
upper bound `ncard ≤ 9`, and then every point is on exactly two guide lines. -/
theorem m6_point_on_two_of_diagExc (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (HPnd : m3HPnd T) (HD : m3DiagExc T) :
    ∀ q : ConstellationIndex,
      {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2 :=
  m6_point_on_two_of_ncard_le T h (m3_guideLines_ncard_le_nine T h HPnd HD)

/-- **The root statement from the nine diagonal rows** — the shape in which the diagonal
exclusions are actually produced (`M5P22.row22`, `M5R11.row11_of_rows`, …):
no guide line carries both `red(i,j)` and `red(i+1,j+1)` for any `(i,j)`. -/
theorem m6_point_on_two_of_rows (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint)
    (hrow : ∀ (i j : TrisectorLabel) (ℓ : Line E), ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (m5_redPt T (i, j)) ∧ ℓ.mem (m5_redPt T (i + 1, j + 1)))) :
    ∀ q : ConstellationIndex,
      {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2 :=
  m6_point_on_two_of_ncard_le T h (m2_guideLines_ncard_le_nine_of_rows T h hrow)

end OrientedTriangle
end XamboMorley
