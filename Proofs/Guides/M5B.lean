import XamboMorleyBase
open XamboMorley
open XamboMorley.OrientedTriangle
open Function Set

set_option maxHeartbeats 2000000

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
variable {o : Orientation ℝ E (Fin 2)}

noncomputable abbrev m5Side (T : OrientedTriangle E o) (d : TrisectorLabel) : E :=
  XamboMorley.OrientedTriangle.OrientedTriangle.m3pSide T d

/-! ### Bridge: every equal-sum red pair joins in a Morley-side direction -/

theorem m5_par12_0_f (T : OrientedTriangle E o) :
    Parallel (m5Side T 2) (m5_redPt T (1, 2) - m5_redPt T (0, 0)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par12 T 0
  rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide,
      show ((0 : TrisectorLabel) + 1) = 1 from by decide] at hp
  simpa [m5_redPt, m5Side] using hp

theorem m5_par12_0_r (T : OrientedTriangle E o) :
    Parallel (m5Side T 2) (m5_redPt T (0, 0) - m5_redPt T (1, 2)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par12 T 0
  rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide,
      show ((0 : TrisectorLabel) + 1) = 1 from by decide] at hp
  simpa [m5_redPt, m5Side] using m1m_par_neg_sub hp

theorem m5_par23_0_f (T : OrientedTriangle E o) :
    Parallel (m5Side T 1) (m5_redPt T (2, 1) - m5_redPt T (1, 2)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par23 T 0
  rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide,
      show ((0 : TrisectorLabel) + 1) = 1 from by decide] at hp
  simpa [m5_redPt, m5Side] using hp

theorem m5_par23_0_r (T : OrientedTriangle E o) :
    Parallel (m5Side T 1) (m5_redPt T (1, 2) - m5_redPt T (2, 1)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par23 T 0
  rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide,
      show ((0 : TrisectorLabel) + 1) = 1 from by decide] at hp
  simpa [m5_redPt, m5Side] using m1m_par_neg_sub hp

theorem m5_par31_0_f (T : OrientedTriangle E o) :
    Parallel (m5Side T 0) (m5_redPt T (0, 0) - m5_redPt T (2, 1)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par31 T 0
  rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide] at hp
  simpa [m5_redPt, m5Side] using hp

theorem m5_par31_0_r (T : OrientedTriangle E o) :
    Parallel (m5Side T 0) (m5_redPt T (2, 1) - m5_redPt T (0, 0)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par31 T 0
  rw [show ((0 : TrisectorLabel) + 2) = 2 from by decide] at hp
  simpa [m5_redPt, m5Side] using m1m_par_neg_sub hp

theorem m5_par12_1_f (T : OrientedTriangle E o) :
    Parallel (m5Side T 0) (m5_redPt T (2, 2) - m5_redPt T (1, 0)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par12 T 1
  rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide,
      show ((1 : TrisectorLabel) + 1) = 2 from by decide] at hp
  simpa [m5_redPt, m5Side] using hp

theorem m5_par12_1_r (T : OrientedTriangle E o) :
    Parallel (m5Side T 0) (m5_redPt T (1, 0) - m5_redPt T (2, 2)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par12 T 1
  rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide,
      show ((1 : TrisectorLabel) + 1) = 2 from by decide] at hp
  simpa [m5_redPt, m5Side] using m1m_par_neg_sub hp

theorem m5_par23_1_f (T : OrientedTriangle E o) :
    Parallel (m5Side T 2) (m5_redPt T (0, 1) - m5_redPt T (2, 2)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par23 T 1
  rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide,
      show ((1 : TrisectorLabel) + 1) = 2 from by decide] at hp
  simpa [m5_redPt, m5Side] using hp

theorem m5_par23_1_r (T : OrientedTriangle E o) :
    Parallel (m5Side T 2) (m5_redPt T (2, 2) - m5_redPt T (0, 1)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par23 T 1
  rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide,
      show ((1 : TrisectorLabel) + 1) = 2 from by decide] at hp
  simpa [m5_redPt, m5Side] using m1m_par_neg_sub hp

theorem m5_par31_1_f (T : OrientedTriangle E o) :
    Parallel (m5Side T 1) (m5_redPt T (1, 0) - m5_redPt T (0, 1)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par31 T 1
  rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide] at hp
  simpa [m5_redPt, m5Side] using hp

theorem m5_par31_1_r (T : OrientedTriangle E o) :
    Parallel (m5Side T 1) (m5_redPt T (0, 1) - m5_redPt T (1, 0)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par31 T 1
  rw [show ((1 : TrisectorLabel) + 2) = 0 from by decide] at hp
  simpa [m5_redPt, m5Side] using m1m_par_neg_sub hp

theorem m5_par12_2_f (T : OrientedTriangle E o) :
    Parallel (m5Side T 1) (m5_redPt T (0, 2) - m5_redPt T (2, 0)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par12 T 2
  rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide,
      show ((2 : TrisectorLabel) + 1) = 0 from by decide] at hp
  simpa [m5_redPt, m5Side] using hp

theorem m5_par12_2_r (T : OrientedTriangle E o) :
    Parallel (m5Side T 1) (m5_redPt T (2, 0) - m5_redPt T (0, 2)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par12 T 2
  rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide,
      show ((2 : TrisectorLabel) + 1) = 0 from by decide] at hp
  simpa [m5_redPt, m5Side] using m1m_par_neg_sub hp

theorem m5_par23_2_f (T : OrientedTriangle E o) :
    Parallel (m5Side T 0) (m5_redPt T (1, 1) - m5_redPt T (0, 2)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par23 T 2
  rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide,
      show ((2 : TrisectorLabel) + 1) = 0 from by decide] at hp
  simpa [m5_redPt, m5Side] using hp

theorem m5_par23_2_r (T : OrientedTriangle E o) :
    Parallel (m5Side T 0) (m5_redPt T (0, 2) - m5_redPt T (1, 1)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par23 T 2
  rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide,
      show ((2 : TrisectorLabel) + 1) = 0 from by decide] at hp
  simpa [m5_redPt, m5Side] using m1m_par_neg_sub hp

theorem m5_par31_2_f (T : OrientedTriangle E o) :
    Parallel (m5Side T 2) (m5_redPt T (2, 0) - m5_redPt T (1, 1)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par31 T 2
  rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide] at hp
  simpa [m5_redPt, m5Side] using hp

theorem m5_par31_2_r (T : OrientedTriangle E o) :
    Parallel (m5Side T 2) (m5_redPt T (1, 1) - m5_redPt T (2, 0)) := by
  have hp := XamboMorley.OrientedTriangle.OrientedTriangle.m3p_red_par31 T 2
  rw [show ((2 : TrisectorLabel) + 2) = 1 from by decide] at hp
  simpa [m5_redPt, m5Side] using m1m_par_neg_sub hp

/-! ### The bridge for an arbitrary equal-sum pair -/

theorem m5_eqsum_par (T : OrientedTriangle E o) (p q : TrisectorLabel × TrisectorLabel)
    (hpq : p ≠ q) (hsum : p.1 + p.2 = q.1 + q.2) :
    Parallel (m5Side T (pairDirection p q)) (m5_redPt T q - m5_redPt T p) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  rcases zmod3_cases a with rfl | rfl | rfl <;>
  rcases zmod3_cases b with rfl | rfl | rfl <;>
  rcases zmod3_cases c with rfl | rfl | rfl <;>
  rcases zmod3_cases d with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hpq
    | (rw [show pairDirection (1, 2) (0, 0) = 2 from by decide]
       exact m5_par12_0_r T)
    | (rw [show pairDirection (0, 0) (1, 2) = 2 from by decide]
       exact m5_par12_0_f T)
    | (rw [show pairDirection (2, 1) (1, 2) = 1 from by decide]
       exact m5_par23_0_r T)
    | (rw [show pairDirection (1, 2) (2, 1) = 1 from by decide]
       exact m5_par23_0_f T)
    | (rw [show pairDirection (0, 0) (2, 1) = 0 from by decide]
       exact m5_par31_0_r T)
    | (rw [show pairDirection (2, 1) (0, 0) = 0 from by decide]
       exact m5_par31_0_f T)
    | (rw [show pairDirection (2, 2) (1, 0) = 0 from by decide]
       exact m5_par12_1_r T)
    | (rw [show pairDirection (1, 0) (2, 2) = 0 from by decide]
       exact m5_par12_1_f T)
    | (rw [show pairDirection (0, 1) (2, 2) = 2 from by decide]
       exact m5_par23_1_r T)
    | (rw [show pairDirection (2, 2) (0, 1) = 2 from by decide]
       exact m5_par23_1_f T)
    | (rw [show pairDirection (1, 0) (0, 1) = 1 from by decide]
       exact m5_par31_1_r T)
    | (rw [show pairDirection (0, 1) (1, 0) = 1 from by decide]
       exact m5_par31_1_f T)
    | (rw [show pairDirection (0, 2) (2, 0) = 1 from by decide]
       exact m5_par12_2_r T)
    | (rw [show pairDirection (2, 0) (0, 2) = 1 from by decide]
       exact m5_par12_2_f T)
    | (rw [show pairDirection (1, 1) (0, 2) = 0 from by decide]
       exact m5_par23_2_r T)
    | (rw [show pairDirection (0, 2) (1, 1) = 0 from by decide]
       exact m5_par23_2_f T)
    | (rw [show pairDirection (2, 0) (1, 1) = 2 from by decide]
       exact m5_par31_2_r T)
    | (rw [show pairDirection (1, 1) (2, 0) = 2 from by decide]
       exact m5_par31_2_f T)
    | exact absurd hsum (by decide)

/-! ### Arithmetic: the diagonal (missing) direction of a label pair -/

noncomputable def m5c (d : TrisectorLabel) : TrisectorLabel := if d = 0 then 1 else if d = 1 then 0 else 2

theorem m5_exists_partner (d : TrisectorLabel) (p : TrisectorLabel × TrisectorLabel)
    (h : p.2 - p.1 ≠ m5c d) :
    ∃ r : TrisectorLabel × TrisectorLabel,
      r ≠ p ∧ p.1 + p.2 = r.1 + r.2 ∧ pairDirection p r = d := by
  revert h
  revert p d
  decide

theorem m5_diag_no_partner (d : TrisectorLabel) (p : TrisectorLabel × TrisectorLabel)
    (h : p.2 - p.1 = m5c d) (r : TrisectorLabel × TrisectorLabel) (hne : r ≠ p)
    (hsum : p.1 + p.2 = r.1 + r.2) : pairDirection p r ≠ d := by
  revert h hne hsum
  revert p r d
  decide

/-! ### Line geometry helpers -/

theorem m5_par_of_mem {ℓ : Line E} {X Y : E} (hX : ℓ.mem X) (hY : ℓ.mem Y) :
    Parallel ℓ.direction (Y - X) := by
  obtain ⟨s, hs⟩ := (Line.mem_iff_parallel ℓ X).mp hX
  obtain ⟨t, ht⟩ := (Line.mem_iff_parallel ℓ Y).mp hY
  exact ⟨t - s, by rw [show Y - X = (Y - ℓ.base) - (X - ℓ.base) from by abel, ht, hs, sub_smul]⟩

/-- If `X ∈ ℓ`, `M` is a direction of `ℓ` and `Y - X` is parallel to `M`, then `Y ∈ ℓ`. -/
theorem m5_mem_of_mem_of_dir {ℓ : Line E} {M : E} {X Y : E} (hX : ℓ.mem X)
    (hd : Parallel M ℓ.direction) (hj : Parallel M (Y - X)) : ℓ.mem Y := by
  obtain ⟨c, hc⟩ := hd
  obtain ⟨e, he⟩ := hj
  obtain ⟨s, hs⟩ := (Line.mem_iff_parallel ℓ X).mp hX
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact ℓ.direction_ne_zero hc
  have hscalar : e + s * c = (e / c + s) * c := by field_simp
  refine (Line.mem_iff_parallel ℓ Y).mpr ⟨e / c + s, ?_⟩
  calc Y - ℓ.base = (Y - X) + (X - ℓ.base) := by abel
    _ = e • M + s • ℓ.direction := by rw [he, hs]
    _ = e • M + s • (c • M) := by rw [hc]
    _ = e • M + (s * c) • M := by rw [smul_smul]
    _ = (e + s * c) • M := by rw [add_smul]
    _ = ((e / c + s) * c) • M := by rw [hscalar]
    _ = (e / c + s) • (c • M) := by rw [smul_smul]
    _ = (e / c + s) • ℓ.direction := by rw [hc]

/-! ### A guide line's two red points: equal sums, or the same diagonal -/

theorem m5_guide_red_pair (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {ℓ : Line E} (hℓ : ℓ ∈ T.guideLines) {p q : TrisectorLabel × TrisectorLabel}
    (hpq : p ≠ q) (hp : ℓ.mem (m5_redPt T p)) (hq : ℓ.mem (m5_redPt T q)) :
    p.1 + p.2 = q.1 + q.2 ∨ p.2 - p.1 = q.2 - q.1 := by
  by_cases hs : p.1 + p.2 = q.1 + q.2
  · exact Or.inl hs
  right
  obtain ⟨d, hd⟩ : ∃ d : TrisectorLabel, Parallel (m5Side T d) ℓ.direction := by
    rcases hℓ.1.1 with h' | h' | h'
    · exact ⟨0, by rw [m5Side, XamboMorley.OrientedTriangle.OrientedTriangle.m3p_side_zero]; exact h'⟩
    · exact ⟨1, by rw [m5Side, XamboMorley.OrientedTriangle.OrientedTriangle.m3p_side_one]; exact h'⟩
    · exact ⟨2, by rw [m5Side, XamboMorley.OrientedTriangle.OrientedTriangle.m3p_side_two]; exact h'⟩
  have key : ∀ x : TrisectorLabel × TrisectorLabel, (x = p ∨ x = q) → x.2 - x.1 = m5c d := by
    intro x hx
    by_contra hx'
    obtain ⟨r, hrne, hrsum, hrdir⟩ := m5_exists_partner d x hx'
    have hxmem : ℓ.mem (m5_redPt T x) := by rcases hx with rfl | rfl <;> assumption
    have hpar : Parallel (m5Side T d) (m5_redPt T r - m5_redPt T x) := by
      rw [← hrdir]
      exact m5_eqsum_par T x r hrne.symm hrsum
    have hrmem : ℓ.mem (m5_redPt T r) := m5_mem_of_mem_of_dir hxmem hd hpar
    have hrp : r ≠ p := by
      rcases hx with hx | hx
      · rw [hx] at hrne
        exact hrne
      · intro hc
        rw [hx, hc] at hrsum
        exact hs hrsum.symm
    have hrq : r ≠ q := by
      rcases hx with hx | hx
      · intro hc
        rw [hx, hc] at hrsum
        exact hs hrsum
      · rw [hx] at hrne
        exact hrne
    have hset : ({⟨.red, p.1, p.2⟩, ⟨.red, q.1, q.2⟩, ⟨.red, r.1, r.2⟩} : Set ConstellationIndex)
        ⊆ {z : ConstellationIndex | z.color = .red ∧ ℓ.mem (T.constellationPoint z)} := by
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨rfl, hp⟩
      · exact ⟨rfl, hq⟩
      · exact ⟨rfl, hrmem⟩
    have e1 : (⟨.red, p.1, p.2⟩ : ConstellationIndex) ≠ ⟨.red, q.1, q.2⟩ := by
      intro hc
      exact hpq (Prod.ext (congrArg ConstellationIndex.first hc) (congrArg ConstellationIndex.second hc))
    have e2 : (⟨.red, p.1, p.2⟩ : ConstellationIndex) ≠ ⟨.red, r.1, r.2⟩ := by
      intro hc
      exact hrp (Prod.ext (congrArg ConstellationIndex.first hc).symm
        (congrArg ConstellationIndex.second hc).symm)
    have e3 : (⟨.red, q.1, q.2⟩ : ConstellationIndex) ≠ ⟨.red, r.1, r.2⟩ := by
      intro hc
      exact hrq (Prod.ext (congrArg ConstellationIndex.first hc).symm
        (congrArg ConstellationIndex.second hc).symm)
    have hcard3 : ({⟨.red, p.1, p.2⟩, ⟨.red, q.1, q.2⟩, ⟨.red, r.1, r.2⟩} :
        Set ConstellationIndex).ncard = 3 := by
      have n1 : (⟨.red, p.1, p.2⟩ : ConstellationIndex) ∉
          ({⟨.red, q.1, q.2⟩, ⟨.red, r.1, r.2⟩} : Set ConstellationIndex) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact fun hc => hc.elim e1 e2
      have n2 : (⟨.red, q.1, q.2⟩ : ConstellationIndex) ∉
          ({⟨.red, r.1, r.2⟩} : Set ConstellationIndex) := by
        simpa using e3
      rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_singleton]
    have hle := Set.ncard_le_ncard hset (Set.toFinite _)
    rw [hcard3, hℓ.1.2.2 TrisectorColor.red] at hle
    omega
  have h1 := key p (Or.inl rfl)
  have h2 := key q (Or.inr rfl)
  rw [h1, h2]

/-- **The upper bound from the nine diagonal exclusions.**  If no guide line carries two
red points of one diagonal class, then there are at most nine guide lines. -/
theorem m5_ncard_le_nine_of_no_diag (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hnd : ∀ (p q : TrisectorLabel × TrisectorLabel), p.2 - p.1 = q.2 - q.1 →
      p.1 + p.2 ≠ q.1 + q.2 → ∀ (ℓ : Line E), ℓ ∈ T.guideLines →
        ¬ (ℓ.mem (m5_redPt T p) ∧ ℓ.mem (m5_redPt T q))) :
    T.guideLines.ncard ≤ 9 := by
  refine m5_ncard_le_nine T h ?_
  intro ℓ hℓ p q hp hq
  by_cases hpq : p = q
  · rw [hpq]
  · by_cases hsum : p.1 + p.2 = q.1 + q.2
    · exact hsum
    · rcases m5_guide_red_pair T h hℓ hpq hp hq with hcase | hcase
      · exact absurd hcase hsum
      · exact absurd ⟨hp, hq⟩ (hnd p q hcase hsum ℓ hℓ)

/-- Two distinct points with equal label sums are not on a common diagonal. -/
theorem m5_diag_ne_sum (p q : TrisectorLabel × TrisectorLabel) (h : p.2 - p.1 = q.2 - q.1)
    (hpq : p ≠ q) : p.1 + p.2 ≠ q.1 + q.2 := by
  revert h
  revert p q
  decide

/-- The reduction in its directly usable form: it suffices to exclude the nine diagonal
joins (a join is a guide line only if it is parallel to a Morley side). -/
theorem m5_ncard_le_nine_of_diag_join (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hnd : ∀ (p q : TrisectorLabel × TrisectorLabel), p ≠ q → p.2 - p.1 = q.2 - q.1 →
      ∀ (ℓ : Line E), ℓ ∈ T.guideLines →
        ¬ (ℓ.mem (m5_redPt T p) ∧ ℓ.mem (m5_redPt T q))) :
    T.guideLines.ncard ≤ 9 := by
  refine m5_ncard_le_nine_of_no_diag T h ?_
  intro p q hdiag hsum ℓ hℓ
  exact hnd p q (fun hc => hsum (by rw [hc])) hdiag ℓ hℓ
