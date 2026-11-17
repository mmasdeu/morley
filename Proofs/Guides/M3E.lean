/-
  Member m3 (swarm smwh7aexl), direction d5.

  Part E: `guideLines_direction_card` from the two exclusion hypotheses of M3G.  Given the
  nine lines of M3C2 (hence `guideLines.ncard = 9`) and the three lines in each Morley-side
  direction, the three direction classes cover `guideLines`, are pairwise disjoint, and each
  has at least three elements, so each has exactly three.
-/
import M3D

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

theorem m3_side0_ne (T : OrientedTriangle E o) : m3pSide T (0 : TrisectorLabel) ≠ 0 :=
  m2_Y_sub_X_ne T

theorem m3_side1_ne (T : OrientedTriangle E o) : m3pSide T (1 : TrisectorLabel) ≠ 0 := by
  rw [m3p_side_one]; exact m2_Z_sub_Y_ne T

theorem m3_side2_ne (T : OrientedTriangle E o) : m3pSide T (2 : TrisectorLabel) ≠ 0 := by
  rw [m3p_side_two]
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

/-- The three lines of a given side direction that lie among the nine. -/
def m3dirLines (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (d : TrisectorLabel) : Set (Line E) :=
  if d = 0 then {T.m3LA0 h, T.m3LC2 h, T.m3LB1 h}
  else if d = 1 then {T.m3LA1 h, T.m3LB2 h, T.m3LC0 h}
  else {T.m3LB0 h, T.m3LC1 h, T.m3LA2 h}

theorem m3dirLines_sub (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) (d : TrisectorLabel) :
    m3dirLines T h d ⊆ {ℓ ∈ T.guideLines | Parallel (m3pSide T d) ℓ.direction} := by
  intro ℓ hℓ
  unfold m3dirLines at hℓ
  have hgl : ∀ (n : Line E), n = T.m3LA0 h ∨ n = T.m3LB0 h ∨ n = T.m3LA1 h ∨ n = T.m3LC1 h ∨
      n = T.m3LC2 h ∨ n = T.m3LB2 h ∨ n = T.m3LB1 h ∨ n = T.m3LA2 h ∨ n = T.m3LC0 h →
      n ∈ T.guideLines := by
    rintro n (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨m3LA0_isGuideLine T h (HPnd), m3lineThrough_isCanonical _ _ _⟩
    · exact ⟨m3LB0_isGuideLine T h (HPnd), m3lineThrough_isCanonical _ _ _⟩
    · exact ⟨m3LA1_isGuideLine T h (HPnd), m3lineThrough_isCanonical _ _ _⟩
    · exact ⟨m3LC1_isGuideLine T h (HPnd), m3lineThrough_isCanonical _ _ _⟩
    · exact ⟨m3LC2_isGuideLine T h (HPnd), m3lineThrough_isCanonical _ _ _⟩
    · exact ⟨m3LB2_isGuideLine T h (HPnd), m3lineThrough_isCanonical _ _ _⟩
    · exact ⟨m3LB1_isGuideLine T h (HPnd), m3lineThrough_isCanonical _ _ _⟩
    · exact ⟨m3LA2_isGuideLine T h (HPnd), m3lineThrough_isCanonical _ _ _⟩
    · exact ⟨m3LC0_isGuideLine T h (HPnd), m3lineThrough_isCanonical _ _ _⟩
  rcases zmod3_cases d with rfl | rfl | rfl
  · simp only [if_pos (show ((0 : TrisectorLabel) = 0) from rfl),
      Set.mem_insert_iff, Set.mem_singleton_iff] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact ⟨hgl _ (Or.inl rfl), m3LA0_side T h⟩
    · exact ⟨hgl _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), m3LC2_side T h⟩
    · exact ⟨hgl _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
        m3LB1_side T h⟩
  · simp only [if_neg (show ¬((1 : TrisectorLabel) = 0) from by decide), if_pos rfl,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact ⟨hgl _ (Or.inr (Or.inr (Or.inl rfl))), m3LA1_side T h⟩
    · exact ⟨hgl _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), m3LB2_side T h⟩
    · exact ⟨hgl _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))),
        m3LC0_side T h⟩
  · simp only [if_neg (show ¬((2 : TrisectorLabel) = 0) from by decide),
      if_neg (show ¬((2 : TrisectorLabel) = 1) from by decide),
      Set.mem_insert_iff, Set.mem_singleton_iff] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact ⟨hgl _ (Or.inr (Or.inl rfl)), m3LB0_side T h⟩
    · exact ⟨hgl _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), m3LC1_side T h⟩
    · exact ⟨hgl _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))),
        m3LA2_side T h⟩

theorem m3dirLines_ncard (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) (d : TrisectorLabel) : (m3dirLines T h d).ncard = 3 := by
  rcases zmod3_cases d with rfl | rfl | rfl
  · unfold m3dirLines
    rw [if_pos rfl, Set.ncard_insert_of_notMem (by simp [m3_ne_0_4 T h HPnd, m3_ne_0_6 T h HPnd]),
      Set.ncard_insert_of_notMem (by simp [m3_ne_4_6 T h HPnd]), Set.ncard_singleton]
  · unfold m3dirLines
    rw [if_neg (show ¬((1 : TrisectorLabel) = 0) from by decide), if_pos rfl,
      Set.ncard_insert_of_notMem (by simp [m3_ne_2_5 T h HPnd, m3_ne_2_8 T h HPnd]),
      Set.ncard_insert_of_notMem (by simp [m3_ne_5_8 T h HPnd]), Set.ncard_singleton]
  · unfold m3dirLines
    rw [if_neg (show ¬((2 : TrisectorLabel) = 0) from by decide),
      if_neg (show ¬((2 : TrisectorLabel) = 1) from by decide),
      Set.ncard_insert_of_notMem (by simp [m3_ne_1_3 T h HPnd, m3_ne_1_7 T h HPnd]),
      Set.ncard_insert_of_notMem (by simp [m3_ne_3_7 T h HPnd]), Set.ncard_singleton]

/-- **`guideLines_direction_card` from the exclusion hypotheses**: for each Morley-side direction there are exactly
three guide lines. -/
theorem m3_guideLines_direction_card (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (HPnd : m3HPnd T) (HD : m3DiagExc T) (v : E)
    (hv : v = T.Y - T.X ∨ v = T.Z - T.Y ∨ v = T.X - T.Z) :
    {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard = 3 := by
  classical
  have hfin : T.guideLines.Finite := m4_guideLines_finite T h
  have h9 : T.guideLines.ncard = 9 := m3_guideLines_card T h HPnd HD
  have hge : ∀ w : E, (w = T.Y - T.X ∨ w = T.Z - T.Y ∨ w = T.X - T.Z) →
      3 ≤ {ℓ ∈ T.guideLines | Parallel w ℓ.direction}.ncard := by
    intro w hw
    rcases hw with rfl | rfl | rfl
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
  -- the three direction classes cover and are disjoint
  set A : Set (Line E) := {ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction} with hAdef
  set B : Set (Line E) := {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction} with hBdef
  set C : Set (Line E) := {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction} with hCdef
  have hcover : T.guideLines = A ∪ B ∪ C := by
    rw [hAdef, hBdef, hCdef]
    ext ℓ
    constructor
    · intro hℓ
      obtain ⟨d, hd⟩ := m3_exists_side T hℓ.1.1
      rcases zmod3_cases d with rfl | rfl | rfl
      · rw [m3p_side_zero] at hd
        exact Or.inl (Or.inl ⟨hℓ, hd⟩)
      · rw [m3p_side_one] at hd
        exact Or.inl (Or.inr ⟨hℓ, hd⟩)
      · rw [m3p_side_two] at hd
        exact Or.inr ⟨hℓ, hd⟩
    · rintro ((⟨hℓ, -⟩ | ⟨hℓ, -⟩) | ⟨hℓ, -⟩) <;> exact hℓ
  have hfA : A.Finite := by rw [hAdef]; exact hfin.subset fun ℓ hℓ => hℓ.1
  have hfB : B.Finite := by rw [hBdef]; exact hfin.subset fun ℓ hℓ => hℓ.1
  have hfC : C.Finite := by rw [hCdef]; exact hfin.subset fun ℓ hℓ => hℓ.1
  have hd01 : Disjoint A B := by
    rw [hAdef, hBdef]
    rw [Set.disjoint_left]
    rintro ℓ ⟨-, h1⟩ ⟨-, h2⟩
    rw [← m3p_side_zero] at h1
    rw [← m3p_side_one] at h2
    exact m3_sides_ne_par T (by decide)
      (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero h1 h2)
  have hd2 : Disjoint (A ∪ B) C := by
    rw [hAdef, hBdef, hCdef]
    rw [Set.disjoint_left]
    rintro ℓ (⟨-, h1⟩ | ⟨-, h1⟩) ⟨-, h2⟩
    · rw [← m3p_side_zero] at h1
      rw [← m3p_side_two] at h2
      exact m3_sides_ne_par T (by decide)
        (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero h1 h2)
    · rw [← m3p_side_one] at h1
      rw [← m3p_side_two] at h2
      exact m3_sides_ne_par T (by decide)
        (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero h1 h2)
  have hgeA : 3 ≤ A.ncard := by
    rw [hAdef]
    have hsub := m3dirLines_sub T h HPnd (0 : TrisectorLabel)
    rw [m3p_side_zero] at hsub
    calc 3 = (m3dirLines T h 0).ncard := (m3dirLines_ncard T h HPnd 0).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (hfin.subset fun ℓ hℓ => hℓ.1)
  have hgeB : 3 ≤ B.ncard := by
    rw [hBdef]
    have hsub := m3dirLines_sub T h HPnd (1 : TrisectorLabel)
    rw [m3p_side_one] at hsub
    calc 3 = (m3dirLines T h 1).ncard := (m3dirLines_ncard T h HPnd 1).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (hfin.subset fun ℓ hℓ => hℓ.1)
  have hgeC : 3 ≤ C.ncard := by
    rw [hCdef]
    have hsub := m3dirLines_sub T h HPnd (2 : TrisectorLabel)
    rw [m3p_side_two] at hsub
    calc 3 = (m3dirLines T h 2).ncard := (m3dirLines_ncard T h HPnd 2).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (hfin.subset fun ℓ hℓ => hℓ.1)
  have hsum : A.ncard + B.ncard + C.ncard = 9 := by
    have h1 : T.guideLines.ncard = A.ncard + B.ncard + C.ncard := by
      conv_lhs => rw [hcover]
      rw [m4_ncard_union_of_disjoint (hfA.union hfB) hfC hd2,
        m4_ncard_union_of_disjoint hfA hfB hd01]
    rw [← h1]
    exact h9
  have hA3 : A.ncard = 3 := by omega
  have hB3 : B.ncard = 3 := by omega
  have hC3 : C.ncard = 3 := by omega
  rcases hv with rfl | rfl | rfl
  · rw [← hAdef]; exact hA3
  · rw [← hBdef]; exact hB3
  · rw [← hCdef]; exact hC3

end OrientedTriangle
end XamboMorley
