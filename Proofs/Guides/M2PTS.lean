/-
  member m2, swarm smwha0atu, direction d8.

  `m2_two_guide_lines`: every one of the 27 constellation points lies on (at least) two
  distinct guide lines of the nine constructed in `smwh7aexl/m3/M3B.lean`.  This is the
  input the incidence half of `point_on_two_guideLines` needs: with it, the double count
  `sum over the 9 guide lines of (2 points of a colour) = 18 = sum over the 9 points of
  that colour of (number of guide lines through them)` forces "exactly two" for every
  point.  (The `≤ 2` bound on its own needs the diagonal exclusions.)

  Everything is unconditional apart from `h : Injective T.constellationPoint`, and the
  only axiom input is the compiled `m3HPnd` of `M2ND.lean`.  Axiom check at the bottom.
-/
import M2ND
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

theorem m2_two_guide_lines (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (q : ConstellationIndex) :
    ∃ ℓ₁ ∈ T.guideLines, ∃ ℓ₂ ∈ T.guideLines, ℓ₁ ≠ ℓ₂ ∧
      ℓ₁.mem (T.constellationPoint q) ∧ ℓ₂.mem (T.constellationPoint q) := by
  have HPnd : m3HPnd T := m2_m3HPnd T h
  rcases q with ⟨c, i, j⟩
  rcases c with _ | _ | _
  · rcases zmod3_cases i with rfl | rfl | rfl
    · rcases zmod3_cases j with rfl | rfl | rfl
      · exact ⟨m3LA0 T h, ⟨m3LA0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB0 T h, ⟨m3LB0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_0_1 T h HPnd, (by simpa only [m5_redPt] using m3LA0_base T h), (by simpa only [m5_redPt] using m3LB0_far T h)⟩
      · exact ⟨m3LA1 T h, ⟨m3LA1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC1 T h, ⟨m3LC1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_2_3 T h HPnd, (by simpa only [m5_redPt] using m3LA1_far T h), (by simpa only [m5_redPt] using m3LC1_base T h)⟩
      · exact ⟨m3LC2 T h, ⟨m3LC2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB2 T h, ⟨m3LB2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_4_5 T h HPnd, (by simpa only [m5_redPt] using m3LC2_far T h), (by simpa only [m5_redPt] using m3LB2_base T h)⟩
    · rcases zmod3_cases j with rfl | rfl | rfl
      · exact ⟨m3LA1 T h, ⟨m3LA1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB1 T h, ⟨m3LB1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_2_6 T h HPnd, (by simpa only [m5_redPt] using m3LA1_base T h), (by simpa only [m5_redPt] using m3LB1_far T h)⟩
      · exact ⟨m3LC2 T h, ⟨m3LC2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LA2 T h, ⟨m3LA2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_4_7 T h HPnd, (by simpa only [m5_redPt] using m3LC2_base T h), (by simpa only [m5_redPt] using m3LA2_far T h)⟩
      · exact ⟨m3LB0 T h, ⟨m3LB0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC0 T h, ⟨m3LC0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_1_8 T h HPnd, (by simpa only [m5_redPt] using m3LB0_base T h), (by simpa only [m5_redPt] using m3LC0_far T h)⟩
    · rcases zmod3_cases j with rfl | rfl | rfl
      · exact ⟨m3LB2 T h, ⟨m3LB2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LA2 T h, ⟨m3LA2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_5_7 T h HPnd, (by simpa only [m5_redPt] using m3LB2_far T h), (by simpa only [m5_redPt] using m3LA2_base T h)⟩
      · exact ⟨m3LA0 T h, ⟨m3LA0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC0 T h, ⟨m3LC0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_0_8 T h HPnd, (by simpa only [m5_redPt] using m3LA0_far T h), (by simpa only [m5_redPt] using m3LC0_base T h)⟩
      · exact ⟨m3LC1 T h, ⟨m3LC1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB1 T h, ⟨m3LB1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_3_6 T h HPnd, (by simpa only [m5_redPt] using m3LC1_far T h), (by simpa only [m5_redPt] using m3LB1_base T h)⟩
  · rcases zmod3_cases i with rfl | rfl | rfl
    · rcases zmod3_cases j with rfl | rfl | rfl
      · exact ⟨m3LA0 T h, ⟨m3LA0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB2 T h, ⟨m3LB2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_0_5 T h HPnd, m3LA0_green_0_0 T h, m3LB2_green_0_0 T h⟩
      · exact ⟨m3LA2 T h, ⟨m3LA2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB1 T h, ⟨m3LB1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, (m3_ne_6_7 T h HPnd).symm, m3LA2_green_0_1 T h, m3LB1_green_0_1 T h⟩
      · exact ⟨m3LA1 T h, ⟨m3LA1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB0 T h, ⟨m3LB0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, (m3_ne_1_2 T h HPnd).symm, m3LA1_green_0_2 T h, m3LB0_green_0_2 T h⟩
    · rcases zmod3_cases j with rfl | rfl | rfl
      · exact ⟨m3LA2 T h, ⟨m3LA2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC0 T h, ⟨m3LC0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_7_8 T h HPnd, m3LA2_green_1_0 T h, m3LC0_green_1_0 T h⟩
      · exact ⟨m3LA1 T h, ⟨m3LA1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC2 T h, ⟨m3LC2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_2_4 T h HPnd, m3LA1_green_1_1 T h, m3LC2_green_1_1 T h⟩
      · exact ⟨m3LA0 T h, ⟨m3LA0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC1 T h, ⟨m3LC1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_0_3 T h HPnd, m3LA0_green_1_2 T h, m3LC1_green_1_2 T h⟩
    · rcases zmod3_cases j with rfl | rfl | rfl
      · exact ⟨m3LB0 T h, ⟨m3LB0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC2 T h, ⟨m3LC2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_1_4 T h HPnd, m3LB0_green_2_0 T h, m3LC2_green_2_0 T h⟩
      · exact ⟨m3LB2 T h, ⟨m3LB2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC1 T h, ⟨m3LC1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, (m3_ne_3_5 T h HPnd).symm, m3LB2_green_2_1 T h, m3LC1_green_2_1 T h⟩
      · exact ⟨m3LB1 T h, ⟨m3LB1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC0 T h, ⟨m3LC0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_6_8 T h HPnd, m3LB1_green_2_2 T h, m3LC0_green_2_2 T h⟩
  · rcases zmod3_cases i with rfl | rfl | rfl
    · rcases zmod3_cases j with rfl | rfl | rfl
      · exact ⟨m3LB0 T h, ⟨m3LB0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB2 T h, ⟨m3LB2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_1_5 T h HPnd, m3LB0_blue_0_0 T h, m3LB2_blue_0_0 T h⟩
      · exact ⟨m3LC0 T h, ⟨m3LC0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC2 T h, ⟨m3LC2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, (m3_ne_4_8 T h HPnd).symm, m3LC0_blue_0_1 T h, m3LC2_blue_0_1 T h⟩
      · exact ⟨m3LA0 T h, ⟨m3LA0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LA2 T h, ⟨m3LA2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_0_7 T h HPnd, m3LA0_blue_0_2 T h, m3LA2_blue_0_2 T h⟩
    · rcases zmod3_cases j with rfl | rfl | rfl
      · exact ⟨m3LC1 T h, ⟨m3LC1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC2 T h, ⟨m3LC2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_3_4 T h HPnd, m3LC1_blue_1_0 T h, m3LC2_blue_1_0 T h⟩
      · exact ⟨m3LA1 T h, ⟨m3LA1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LA2 T h, ⟨m3LA2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_2_7 T h HPnd, m3LA1_blue_1_1 T h, m3LA2_blue_1_1 T h⟩
      · exact ⟨m3LB1 T h, ⟨m3LB1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB2 T h, ⟨m3LB2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, (m3_ne_5_6 T h HPnd).symm, m3LB1_blue_1_2 T h, m3LB2_blue_1_2 T h⟩
    · rcases zmod3_cases j with rfl | rfl | rfl
      · exact ⟨m3LA0 T h, ⟨m3LA0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LA1 T h, ⟨m3LA1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_0_2 T h HPnd, m3LA0_blue_2_0 T h, m3LA1_blue_2_0 T h⟩
      · exact ⟨m3LB0 T h, ⟨m3LB0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LB1 T h, ⟨m3LB1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3_ne_1_6 T h HPnd, m3LB0_blue_2_1 T h, m3LB1_blue_2_1 T h⟩
      · exact ⟨m3LC0 T h, ⟨m3LC0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, m3LC1 T h, ⟨m3LC1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩, (m3_ne_3_8 T h HPnd).symm, m3LC0_blue_2_2 T h, m3LC1_blue_2_2 T h⟩
end OrientedTriangle
end XamboMorley

#print axioms XamboMorley.OrientedTriangle.m2_two_guide_lines
