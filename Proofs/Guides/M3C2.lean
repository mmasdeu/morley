/-
  Member m3 (swarm smwh7aexl), direction d5: NINE_EXACT_GUIDE_MEMBERS.

  Part C2: the nine guide lines, their pairwise distinctness and the constructive lower
  bound `9 ≤ guideLines.ncard`, from `m3HPnd` (the non-diagonal exclusion hypothesis of
  `M3G`).  No hypothesis about diagonal pairs is used here: the two known points of each
  colour on each of the nine lines form a non-diagonal equal-sum pair, so the third-point
  exclusion of `m3G`'s `m3_no_third_nd` applies.
-/
import M3G

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set

namespace XamboMorley
namespace OrientedTriangle

open XamboMorley.OrientedTriangle.OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {{o : Orientation ℝ E (Fin 2)}}

/-! ### Counting lemmas -/

theorem m3_colour_split (P : ConstellationIndex → Prop) :
    {q : ConstellationIndex | P q} =
      ({q | q.color = .red ∧ P q} ∪ {q | q.color = .green ∧ P q} ∪
        {q | q.color = .blue ∧ P q}) := by
  ext q
  constructor
  · intro hq
    rcases q with ⟨c, a, b⟩
    cases c
    · exact Or.inl (Or.inl ⟨rfl, hq⟩)
    · exact Or.inl (Or.inr ⟨rfl, hq⟩)
    · exact Or.inr ⟨rfl, hq⟩
  · rintro ((⟨-, hq⟩ | ⟨-, hq⟩) | ⟨-, hq⟩) <;> exact hq

theorem m3_ncard_six (T : OrientedTriangle E o) {ℓ : Line E}
    (hr : {q : ConstellationIndex | q.color = .red ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2)
    (hg : {q : ConstellationIndex | q.color = .green ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2)
    (hb : {q : ConstellationIndex | q.color = .blue ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2) :
    {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)}.ncard = 6 := by
  classical
  rw [m3_colour_split (fun q => ℓ.mem (T.constellationPoint q))]
  have hd1 : Disjoint ({q : ConstellationIndex | q.color = .red ∧ ℓ.mem (T.constellationPoint q)})
      {q : ConstellationIndex | q.color = .green ∧ ℓ.mem (T.constellationPoint q)} := by
    rw [Set.disjoint_left]
    rintro q h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [h1.1] at h2
    exact absurd h2.1 (by decide)
  have hd2 : Disjoint
      (({q : ConstellationIndex | q.color = .red ∧ ℓ.mem (T.constellationPoint q)}) ∪
        {q : ConstellationIndex | q.color = .green ∧ ℓ.mem (T.constellationPoint q)})
      {q : ConstellationIndex | q.color = .blue ∧ ℓ.mem (T.constellationPoint q)} := by
    rw [Set.disjoint_left]
    rintro q h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    rcases h1 with ⟨h1a, -⟩ | ⟨h1a, -⟩
    · rw [h1a] at h2; exact absurd h2.1 (by decide)
    · rw [h1a] at h2; exact absurd h2.1 (by decide)
  rw [m4_ncard_union_of_disjoint (Set.toFinite _) (Set.toFinite _) hd2,
    m4_ncard_union_of_disjoint (Set.toFinite _) (Set.toFinite _) hd1, hr, hg, hb]

/-! ### Distinctness of the nine lines -/

/-- Two lines whose directions are parallel to two different Morley sides are different. -/
theorem m3_ne_of_sides (T : OrientedTriangle E o) {ℓ ℓ' : Line E} {d e : TrisectorLabel}
    (hde : d ≠ e) (h : Parallel (m3pSide T d) ℓ.direction)
    (h' : Parallel (m3pSide T e) ℓ'.direction) : ℓ ≠ ℓ' := by
  rintro rfl
  have hpar : Parallel (m3pSide T d) (m3pSide T e) :=
    m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero h h'
  have hYX : T.Y - T.X ≠ 0 := m2_Y_sub_X_ne T
  have hZY : T.Z - T.Y ≠ 0 := m2_Z_sub_Y_ne T
  have hXZ : T.X - T.Z ≠ 0 := by
    intro h0
    have hdist : dist T.X T.Z = 0 := by
      rw [dist_eq_norm, show T.X - T.Z = 0 from h0, norm_zero]
    have h1 : dist T.Z T.X = 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma :=
      T.morley_side_lengths.2.2
    rw [dist_comm] at hdist
    rw [h1] at hdist
    have hpos : 0 < 4 * T.delta * Real.sin T.alpha * Real.sin T.beta * Real.sin T.gamma := by
      have h2 := m7_delta_pos T
      have h3 := m7_sin_alpha_pos T
      have h4 := m7_sin_beta_pos T
      have h5 := m7_sin_gamma_pos T
      positivity
    linarith
  rcases zmod3_cases d with rfl | rfl | rfl <;> rcases zmod3_cases e with rfl | rfl | rfl
  · exact absurd rfl hde
  · rw [m3p_side_zero, m3p_side_one] at hpar
    exact (m4_not_parallel_morley (o := o) T).1 hpar
  · rw [m3p_side_zero, m3p_side_two] at hpar
    exact (m4_not_parallel_morley (o := o) T).2.2 (parallel_comm hYX hXZ hpar)
  · rw [m3p_side_one, m3p_side_zero] at hpar
    exact (m4_not_parallel_morley (o := o) T).1 (parallel_comm hZY hYX hpar)
  · exact absurd rfl hde
  · rw [m3p_side_one, m3p_side_two] at hpar
    exact (m4_not_parallel_morley (o := o) T).2.1 hpar
  · rw [m3p_side_two, m3p_side_zero] at hpar
    exact (m4_not_parallel_morley (o := o) T).2.2 hpar
  · rw [m3p_side_two, m3p_side_one] at hpar
    exact (m4_not_parallel_morley (o := o) T).2.1 (parallel_comm hXZ hZY hpar)
  · exact absurd rfl hde


/-! ### Each of the nine lines is a guide line (from `m3HPnd`) -/


theorem m3LA0_isGuideLine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : T.IsGuideLine (m3LA0 T h) := by
  have hdir := m3LA0_dir T h
  have hr : {q : ConstellationIndex | q.color = .red ∧ (m3LA0 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .red) (p1 := ⟨0, 0⟩)
      (p2 := ⟨2, 1⟩) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).2) (m3LA0_base T h) (m3LA0_far T h)
  have hg : {q : ConstellationIndex | q.color = .green ∧ (m3LA0 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .green) (p1 := ⟨0, 0⟩)
      (p2 := ⟨1, 2⟩) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LA0_green_0_0 T h) (m3LA0_green_1_2 T h)
  have hb : {q : ConstellationIndex | q.color = .blue ∧ (m3LA0 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .blue) (p1 := ⟨0, 2⟩)
      (p2 := ⟨2, 0⟩) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LA0_blue_0_2 T h) (m3LA0_blue_2_0 T h)
  refine ⟨hdir, m3_ncard_six T hr hg hb, ?_⟩
  intro c
  cases c
  · exact hr
  · exact hg
  · exact hb


theorem m3LB0_isGuideLine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : T.IsGuideLine (m3LB0 T h) := by
  have hdir := m3LB0_dir T h
  have hr : {q : ConstellationIndex | q.color = .red ∧ (m3LB0 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .red) (p1 := ⟨1, 2⟩)
      (p2 := ⟨0, 0⟩) (by decide : (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel) (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).2) (m3LB0_base T h) (m3LB0_far T h)
  have hg : {q : ConstellationIndex | q.color = .green ∧ (m3LB0 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .green) (p1 := ⟨0, 2⟩)
      (p2 := ⟨2, 0⟩) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LB0_green_0_2 T h) (m3LB0_green_2_0 T h)
  have hb : {q : ConstellationIndex | q.color = .blue ∧ (m3LB0 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .blue) (p1 := ⟨0, 0⟩)
      (p2 := ⟨2, 1⟩) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LB0_blue_0_0 T h) (m3LB0_blue_2_1 T h)
  refine ⟨hdir, m3_ncard_six T hr hg hb, ?_⟩
  intro c
  cases c
  · exact hr
  · exact hg
  · exact hb


theorem m3LA1_isGuideLine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : T.IsGuideLine (m3LA1 T h) := by
  have hdir := m3LA1_dir T h
  have hr : {q : ConstellationIndex | q.color = .red ∧ (m3LA1 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .red) (p1 := ⟨1, 0⟩)
      (p2 := ⟨0, 1⟩) (by decide : (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel) (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).2) (m3LA1_base T h) (m3LA1_far T h)
  have hg : {q : ConstellationIndex | q.color = .green ∧ (m3LA1 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .green) (p1 := ⟨0, 2⟩)
      (p2 := ⟨1, 1⟩) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LA1_green_0_2 T h) (m3LA1_green_1_1 T h)
  have hb : {q : ConstellationIndex | q.color = .blue ∧ (m3LA1 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .blue) (p1 := ⟨1, 1⟩)
      (p2 := ⟨2, 0⟩) (by decide : (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LA1_blue_1_1 T h) (m3LA1_blue_2_0 T h)
  refine ⟨hdir, m3_ncard_six T hr hg hb, ?_⟩
  intro c
  cases c
  · exact hr
  · exact hg
  · exact hb


theorem m3LC1_isGuideLine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : T.IsGuideLine (m3LC1 T h) := by
  have hdir := m3LC1_dir T h
  have hr : {q : ConstellationIndex | q.color = .red ∧ (m3LC1 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .red) (p1 := ⟨0, 1⟩)
      (p2 := ⟨2, 2⟩) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).2) (m3LC1_base T h) (m3LC1_far T h)
  have hg : {q : ConstellationIndex | q.color = .green ∧ (m3LC1 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .green) (p1 := ⟨1, 2⟩)
      (p2 := ⟨2, 1⟩) (by decide : (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LC1_green_1_2 T h) (m3LC1_green_2_1 T h)
  have hb : {q : ConstellationIndex | q.color = .blue ∧ (m3LC1 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .blue) (p1 := ⟨1, 0⟩)
      (p2 := ⟨2, 2⟩) (by decide : (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LC1_blue_1_0 T h) (m3LC1_blue_2_2 T h)
  refine ⟨hdir, m3_ncard_six T hr hg hb, ?_⟩
  intro c
  cases c
  · exact hr
  · exact hg
  · exact hb


theorem m3LC2_isGuideLine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : T.IsGuideLine (m3LC2 T h) := by
  have hdir := m3LC2_dir T h
  have hr : {q : ConstellationIndex | q.color = .red ∧ (m3LC2 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .red) (p1 := ⟨1, 1⟩)
      (p2 := ⟨0, 2⟩) (by decide : (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel) (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).2) (m3LC2_base T h) (m3LC2_far T h)
  have hg : {q : ConstellationIndex | q.color = .green ∧ (m3LC2 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .green) (p1 := ⟨1, 1⟩)
      (p2 := ⟨2, 0⟩) (by decide : (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LC2_green_1_1 T h) (m3LC2_green_2_0 T h)
  have hb : {q : ConstellationIndex | q.color = .blue ∧ (m3LC2 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .blue) (p1 := ⟨0, 1⟩)
      (p2 := ⟨1, 0⟩) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LC2_blue_0_1 T h) (m3LC2_blue_1_0 T h)
  refine ⟨hdir, m3_ncard_six T hr hg hb, ?_⟩
  intro c
  cases c
  · exact hr
  · exact hg
  · exact hb


theorem m3LB2_isGuideLine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : T.IsGuideLine (m3LB2 T h) := by
  have hdir := m3LB2_dir T h
  have hr : {q : ConstellationIndex | q.color = .red ∧ (m3LB2 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .red) (p1 := ⟨0, 2⟩)
      (p2 := ⟨2, 0⟩) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).2) (m3LB2_base T h) (m3LB2_far T h)
  have hg : {q : ConstellationIndex | q.color = .green ∧ (m3LB2 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .green) (p1 := ⟨0, 0⟩)
      (p2 := ⟨2, 1⟩) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LB2_green_0_0 T h) (m3LB2_green_2_1 T h)
  have hb : {q : ConstellationIndex | q.color = .blue ∧ (m3LB2 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .blue) (p1 := ⟨0, 0⟩)
      (p2 := ⟨1, 2⟩) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LB2_blue_0_0 T h) (m3LB2_blue_1_2 T h)
  refine ⟨hdir, m3_ncard_six T hr hg hb, ?_⟩
  intro c
  cases c
  · exact hr
  · exact hg
  · exact hb


theorem m3LB1_isGuideLine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : T.IsGuideLine (m3LB1 T h) := by
  have hdir := m3LB1_dir T h
  have hr : {q : ConstellationIndex | q.color = .red ∧ (m3LB1 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .red) (p1 := ⟨2, 2⟩)
      (p2 := ⟨1, 0⟩) (by decide : (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel) (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).2) (m3LB1_base T h) (m3LB1_far T h)
  have hg : {q : ConstellationIndex | q.color = .green ∧ (m3LB1 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .green) (p1 := ⟨0, 1⟩)
      (p2 := ⟨2, 2⟩) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LB1_green_0_1 T h) (m3LB1_green_2_2 T h)
  have hb : {q : ConstellationIndex | q.color = .blue ∧ (m3LB1 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .blue) (p1 := ⟨1, 2⟩)
      (p2 := ⟨2, 1⟩) (by decide : (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LB1_blue_1_2 T h) (m3LB1_blue_2_1 T h)
  refine ⟨hdir, m3_ncard_six T hr hg hb, ?_⟩
  intro c
  cases c
  · exact hr
  · exact hg
  · exact hb


theorem m3LA2_isGuideLine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : T.IsGuideLine (m3LA2 T h) := by
  have hdir := m3LA2_dir T h
  have hr : {q : ConstellationIndex | q.color = .red ∧ (m3LA2 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .red) (p1 := ⟨2, 0⟩)
      (p2 := ⟨1, 1⟩) (by decide : (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel) (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).2) (m3LA2_base T h) (m3LA2_far T h)
  have hg : {q : ConstellationIndex | q.color = .green ∧ (m3LA2 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .green) (p1 := ⟨0, 1⟩)
      (p2 := ⟨1, 0⟩) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LA2_green_0_1 T h) (m3LA2_green_1_0 T h)
  have hb : {q : ConstellationIndex | q.color = .blue ∧ (m3LA2 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .blue) (p1 := ⟨0, 2⟩)
      (p2 := ⟨1, 1⟩) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LA2_blue_0_2 T h) (m3LA2_blue_1_1 T h)
  refine ⟨hdir, m3_ncard_six T hr hg hb, ?_⟩
  intro c
  cases c
  · exact hr
  · exact hg
  · exact hb


theorem m3LC0_isGuideLine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : T.IsGuideLine (m3LC0 T h) := by
  have hdir := m3LC0_dir T h
  have hr : {q : ConstellationIndex | q.color = .red ∧ (m3LC0 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .red) (p1 := ⟨2, 1⟩)
      (p2 := ⟨1, 2⟩) (by decide : (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel) (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel).2) (m3LC0_base T h) (m3LC0_far T h)
  have hg : {q : ConstellationIndex | q.color = .green ∧ (m3LC0 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .green) (p1 := ⟨1, 0⟩)
      (p2 := ⟨2, 2⟩) (by decide : (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LC0_green_1_0 T h) (m3LC0_green_2_2 T h)
  have hb : {q : ConstellationIndex | q.color = .blue ∧ (m3LC0 T h).mem (T.constellationPoint q)}.ncard = 2 :=
    m3_colour_two_nd T h HPnd hdir (cc := .blue) (p1 := ⟨0, 1⟩)
      (p2 := ⟨2, 2⟩) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : ¬ m3Diag (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel)) (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel).2 = (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).1 + (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel).2)
      (m3LC0_blue_0_1 T h) (m3LC0_blue_2_2 T h)
  refine ⟨hdir, m3_ncard_six T hr hg hb, ?_⟩
  intro c
  cases c
  · exact hr
  · exact hg
  · exact hb

/-! ### The nine lines are pairwise distinct (from `m3HPnd`) -/


theorem m3_ne_0_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA0 T h ≠ m3LB0 T h :=
  m3_ne_of_sides T (by decide) (m3LA0_side T h) (m3LB0_side T h)


theorem m3_ne_0_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA0 T h ≠ m3LA1 T h :=
  m3_ne_of_sides T (by decide) (m3LA0_side T h) (m3LA1_side T h)


theorem m3_ne_0_3 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA0 T h ≠ m3LC1 T h :=
  m3_ne_of_sides T (by decide) (m3LA0_side T h) (m3LC1_side T h)


theorem m3_ne_0_4 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA0 T h ≠ m3LC2 T h :=
  m3_ne_of_nd_pair T HPnd (m3LA0_dir T h) (cc := .red) (p := ⟨0, 0⟩)
    (q := ⟨0, 2⟩) (by decide) (by decide) (by decide)
    (m3LA0_base T h) (m3LC2_far T h)


theorem m3_ne_0_5 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA0 T h ≠ m3LB2 T h :=
  m3_ne_of_sides T (by decide) (m3LA0_side T h) (m3LB2_side T h)


theorem m3_ne_0_6 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA0 T h ≠ m3LB1 T h :=
  m3_ne_of_nd_pair T HPnd (m3LA0_dir T h) (cc := .red) (p := ⟨0, 0⟩)
    (q := ⟨1, 0⟩) (by decide) (by decide) (by decide)
    (m3LA0_base T h) (m3LB1_far T h)


theorem m3_ne_0_7 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA0 T h ≠ m3LA2 T h :=
  m3_ne_of_sides T (by decide) (m3LA0_side T h) (m3LA2_side T h)


theorem m3_ne_0_8 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA0 T h ≠ m3LC0 T h :=
  m3_ne_of_sides T (by decide) (m3LA0_side T h) (m3LC0_side T h)


theorem m3_ne_1_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB0 T h ≠ m3LA1 T h :=
  m3_ne_of_sides T (by decide) (m3LB0_side T h) (m3LA1_side T h)


theorem m3_ne_1_3 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB0 T h ≠ m3LC1 T h :=
  m3_ne_of_nd_pair T HPnd (m3LB0_dir T h) (cc := .red) (p := ⟨1, 2⟩)
    (q := ⟨2, 2⟩) (by decide) (by decide) (by decide)
    (m3LB0_base T h) (m3LC1_far T h)


theorem m3_ne_1_4 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB0 T h ≠ m3LC2 T h :=
  m3_ne_of_sides T (by decide) (m3LB0_side T h) (m3LC2_side T h)


theorem m3_ne_1_5 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB0 T h ≠ m3LB2 T h :=
  m3_ne_of_sides T (by decide) (m3LB0_side T h) (m3LB2_side T h)


theorem m3_ne_1_6 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB0 T h ≠ m3LB1 T h :=
  m3_ne_of_sides T (by decide) (m3LB0_side T h) (m3LB1_side T h)


theorem m3_ne_1_7 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB0 T h ≠ m3LA2 T h :=
  m3_ne_of_nd_pair T HPnd (m3LB0_dir T h) (cc := .red) (p := ⟨1, 2⟩)
    (q := ⟨1, 1⟩) (by decide) (by decide) (by decide)
    (m3LB0_base T h) (m3LA2_far T h)


theorem m3_ne_1_8 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB0 T h ≠ m3LC0 T h :=
  m3_ne_of_sides T (by decide) (m3LB0_side T h) (m3LC0_side T h)


theorem m3_ne_2_3 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA1 T h ≠ m3LC1 T h :=
  m3_ne_of_sides T (by decide) (m3LA1_side T h) (m3LC1_side T h)


theorem m3_ne_2_4 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA1 T h ≠ m3LC2 T h :=
  m3_ne_of_sides T (by decide) (m3LA1_side T h) (m3LC2_side T h)


theorem m3_ne_2_5 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA1 T h ≠ m3LB2 T h :=
  m3_ne_of_nd_pair T HPnd (m3LA1_dir T h) (cc := .red) (p := ⟨1, 0⟩)
    (q := ⟨2, 0⟩) (by decide) (by decide) (by decide)
    (m3LA1_base T h) (m3LB2_far T h)


theorem m3_ne_2_6 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA1 T h ≠ m3LB1 T h :=
  m3_ne_of_sides T (by decide) (m3LA1_side T h) (m3LB1_side T h)


theorem m3_ne_2_7 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA1 T h ≠ m3LA2 T h :=
  m3_ne_of_sides T (by decide) (m3LA1_side T h) (m3LA2_side T h)


theorem m3_ne_2_8 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA1 T h ≠ m3LC0 T h :=
  m3_ne_of_nd_pair T HPnd (m3LA1_dir T h) (cc := .red) (p := ⟨1, 0⟩)
    (q := ⟨1, 2⟩) (by decide) (by decide) (by decide)
    (m3LA1_base T h) (m3LC0_far T h)


theorem m3_ne_3_4 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LC1 T h ≠ m3LC2 T h :=
  m3_ne_of_sides T (by decide) (m3LC1_side T h) (m3LC2_side T h)


theorem m3_ne_3_5 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LC1 T h ≠ m3LB2 T h :=
  m3_ne_of_sides T (by decide) (m3LC1_side T h) (m3LB2_side T h)


theorem m3_ne_3_6 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LC1 T h ≠ m3LB1 T h :=
  m3_ne_of_sides T (by decide) (m3LC1_side T h) (m3LB1_side T h)


theorem m3_ne_3_7 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LC1 T h ≠ m3LA2 T h :=
  m3_ne_of_nd_pair T HPnd (m3LC1_dir T h) (cc := .red) (p := ⟨0, 1⟩)
    (q := ⟨1, 1⟩) (by decide) (by decide) (by decide)
    (m3LC1_base T h) (m3LA2_far T h)


theorem m3_ne_3_8 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LC1 T h ≠ m3LC0 T h :=
  m3_ne_of_sides T (by decide) (m3LC1_side T h) (m3LC0_side T h)


theorem m3_ne_4_5 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LC2 T h ≠ m3LB2 T h :=
  m3_ne_of_sides T (by decide) (m3LC2_side T h) (m3LB2_side T h)


theorem m3_ne_4_6 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LC2 T h ≠ m3LB1 T h :=
  m3_ne_of_nd_pair T HPnd (m3LC2_dir T h) (cc := .red) (p := ⟨1, 1⟩)
    (q := ⟨1, 0⟩) (by decide) (by decide) (by decide)
    (m3LC2_base T h) (m3LB1_far T h)


theorem m3_ne_4_7 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LC2 T h ≠ m3LA2 T h :=
  m3_ne_of_sides T (by decide) (m3LC2_side T h) (m3LA2_side T h)


theorem m3_ne_4_8 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LC2 T h ≠ m3LC0 T h :=
  m3_ne_of_sides T (by decide) (m3LC2_side T h) (m3LC0_side T h)


theorem m3_ne_5_6 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB2 T h ≠ m3LB1 T h :=
  m3_ne_of_sides T (by decide) (m3LB2_side T h) (m3LB1_side T h)


theorem m3_ne_5_7 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB2 T h ≠ m3LA2 T h :=
  m3_ne_of_sides T (by decide) (m3LB2_side T h) (m3LA2_side T h)


theorem m3_ne_5_8 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB2 T h ≠ m3LC0 T h :=
  m3_ne_of_nd_pair T HPnd (m3LB2_dir T h) (cc := .red) (p := ⟨0, 2⟩)
    (q := ⟨1, 2⟩) (by decide) (by decide) (by decide)
    (m3LB2_base T h) (m3LC0_far T h)


theorem m3_ne_6_7 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB1 T h ≠ m3LA2 T h :=
  m3_ne_of_sides T (by decide) (m3LB1_side T h) (m3LA2_side T h)


theorem m3_ne_6_8 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LB1 T h ≠ m3LC0 T h :=
  m3_ne_of_sides T (by decide) (m3LB1_side T h) (m3LC0_side T h)


theorem m3_ne_7_8 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : m3LA2 T h ≠ m3LC0 T h :=
  m3_ne_of_sides T (by decide) (m3LA2_side T h) (m3LC0_side T h)


/-! ### The constructive lower bound -/

theorem m3_nine_le_ncard (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) : 9 ≤ T.guideLines.ncard := by
  classical
  have hS9 : (insert (m3LA0 T h) (insert (m3LB0 T h) (insert (m3LA1 T h) (insert (m3LC1 T h) (insert (m3LC2 T h) (insert (m3LB2 T h) (insert (m3LB1 T h) (insert (m3LA2 T h) (insert (m3LC0 T h) (∅ : Set (Line E))))))))))).ncard = 9 := by
    rw [Set.ncard_insert_of_notMem (by simp [m3_ne_0_1 T h HPnd, m3_ne_0_2 T h HPnd, m3_ne_0_3 T h HPnd, m3_ne_0_4 T h HPnd, m3_ne_0_5 T h HPnd, m3_ne_0_6 T h HPnd, m3_ne_0_7 T h HPnd, m3_ne_0_8 T h HPnd]), Set.ncard_insert_of_notMem (by simp [m3_ne_1_2 T h HPnd, m3_ne_1_3 T h HPnd, m3_ne_1_4 T h HPnd, m3_ne_1_5 T h HPnd, m3_ne_1_6 T h HPnd, m3_ne_1_7 T h HPnd, m3_ne_1_8 T h HPnd]), Set.ncard_insert_of_notMem (by simp [m3_ne_2_3 T h HPnd, m3_ne_2_4 T h HPnd, m3_ne_2_5 T h HPnd, m3_ne_2_6 T h HPnd, m3_ne_2_7 T h HPnd, m3_ne_2_8 T h HPnd]), Set.ncard_insert_of_notMem (by simp [m3_ne_3_4 T h HPnd, m3_ne_3_5 T h HPnd, m3_ne_3_6 T h HPnd, m3_ne_3_7 T h HPnd, m3_ne_3_8 T h HPnd]), Set.ncard_insert_of_notMem (by simp [m3_ne_4_5 T h HPnd, m3_ne_4_6 T h HPnd, m3_ne_4_7 T h HPnd, m3_ne_4_8 T h HPnd]), Set.ncard_insert_of_notMem (by simp [m3_ne_5_6 T h HPnd, m3_ne_5_7 T h HPnd, m3_ne_5_8 T h HPnd]), Set.ncard_insert_of_notMem (by simp [m3_ne_6_7 T h HPnd, m3_ne_6_8 T h HPnd]), Set.ncard_insert_of_notMem (by simpa using m3_ne_7_8 T h HPnd), Set.ncard_insert_of_notMem (by simp), Set.ncard_empty]
  have hsub : (insert (m3LA0 T h) (insert (m3LB0 T h) (insert (m3LA1 T h) (insert (m3LC1 T h) (insert (m3LC2 T h) (insert (m3LB2 T h) (insert (m3LB1 T h) (insert (m3LA2 T h) (insert (m3LC0 T h) (∅ : Set (Line E))))))))))) ⊆ T.guideLines := by
    intro ℓ hℓ
    simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

    · exact ⟨m3LA0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩

    · exact ⟨m3LB0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩

    · exact ⟨m3LA1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩

    · exact ⟨m3LC1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩

    · exact ⟨m3LC2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩

    · exact ⟨m3LB2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩

    · exact ⟨m3LB1_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩

    · exact ⟨m3LA2_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩

    · exact ⟨m3LC0_isGuideLine T h HPnd, m3lineThrough_isCanonical _ _ _⟩

  calc 9 = (insert (m3LA0 T h) (insert (m3LB0 T h) (insert (m3LA1 T h) (insert (m3LC1 T h) (insert (m3LC2 T h) (insert (m3LB2 T h) (insert (m3LB1 T h) (insert (m3LA2 T h) (insert (m3LC0 T h) (∅ : Set (Line E))))))))))).ncard := hS9.symm
    _ ≤ T.guideLines.ncard := Set.ncard_le_ncard hsub (m4_guideLines_finite T h)

end OrientedTriangle
end XamboMorley
