/-
  Member m3 (swarm smwh7aexl), direction d5.

  Part G: the *correct* pair-level hypothesis for the guide-line count, split into the two
  classes that are actually true, and the counting bridge from them.

  The earlier draft of this direction used a single all-pairs hypothesis ("no same-colour
  unequal-sum join is parallel to a Morley side").  That statement is FALSE: at special
  triangles the two diagonal pairs {(0,1),(1,2)} and {(1,0),(2,1)} do have side-parallel
  joins (see the compiled counterexample of the earlier swarm's m5).  The two classes used
  here are

  * `m3HPnd`  — the 18 NON-diagonal unequal-sum pairs are never side-parallel (true; this
    is what the "7 simple + 18 non-diagonal" exact-algebra certificates establish);
  * `m3DiagExc` — for the 9 diagonal pairs, no *guide line* carries both red points.  This
    is the M5B `no_diag` form: the seven never-side-parallel pairs give it directly, and
    the two exceptional pairs are excluded by the two-colour (green/blue) test, not by a
    parallelism statement.

  `m3HPnd` alone gives the constructive lower bound (nine guide lines), `m3HPnd` together
  with `m3DiagExc` gives `hclass`, hence the upper bound and `guideLines.ncard = 9`.
-/
import M3B

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

/-- `p` and `q` are a *diagonal* pair: equal difference of the labels. -/
abbrev m3Diag (p q : TrisectorLabel × TrisectorLabel) : Prop := p.2 - p.1 = q.2 - q.1

/-- **Non-diagonal exclusion hypothesis.**  Two distinct same-colour constellation points
whose label sums differ and whose label differences differ never have a join parallel to a
Morley side.  (18 label pairs per colour; true for every triangle.) -/
def m3HPnd (T : OrientedTriangle E o) : Prop :=
  ∀ (c : TrisectorColor) (p q : TrisectorLabel × TrisectorLabel), p ≠ q →
    p.1 + p.2 ≠ q.1 + q.2 → ¬ m3Diag p q → ∀ d : TrisectorLabel,
      ¬ Parallel (m3pSide T d)
        (T.constellationPoint ⟨c, q.1, q.2⟩ - T.constellationPoint ⟨c, p.1, p.2⟩)

/-- **Diagonal exclusion hypothesis (M5B `no_diag` form).**  No guide line carries two red
constellation points which form a diagonal pair (equal difference of labels); for the nine
such pairs the label sums are automatically different. -/
def m3DiagExc (T : OrientedTriangle E o) : Prop :=
  ∀ (p q : TrisectorLabel × TrisectorLabel), p ≠ q → m3Diag p q →
    ∀ ℓ : Line E, ℓ ∈ T.guideLines →
      ¬ (ℓ.mem (T.m5_redPt p) ∧ ℓ.mem (T.m5_redPt q))

/-- `parallelToMorleySide` is the same as being parallel to one of the three `m3pSide`s. -/
theorem m3_exists_side (T : OrientedTriangle E o) {v : E}
    (h : T.parallelToMorleySide v) : ∃ d : TrisectorLabel, Parallel (m3pSide T d) v := by
  rcases h with h | h | h
  · exact ⟨0, by rwa [m3p_side_zero]⟩
  · exact ⟨1, by rwa [m3p_side_one]⟩
  · exact ⟨2, by rwa [m3p_side_two]⟩

/-- Two different Morley sides are not parallel. -/
theorem m3_sides_ne_par (T : OrientedTriangle E o) {d e : TrisectorLabel} (hde : d ≠ e) :
    ¬ Parallel (m3pSide T d) (m3pSide T e) := by
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
  intro hpar
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

/-- The three labels of one sum class `s` are `(s,0)`, `(s+1,2)`, `(s+2,1)`. -/
theorem m3_sumclass_mem (a b s : TrisectorLabel) (h : a + b = s) :
    ((a, b) : TrisectorLabel × TrisectorLabel) = (s, 0) ∨
      (a, b) = (s + 1, 2) ∨ (a, b) = (s + 2, 1) := by
  revert h
  revert a b s
  decide

/-- Three distinct labels with the same sum `s` are exactly the three labels of the sum
class, so each of `(s,0)`, `(s+1,2)`, `(s+2,1)` is one of them. -/
theorem m3_sumclass_cover (p1 p2 p3 : TrisectorLabel × TrisectorLabel) (s : TrisectorLabel)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (hs1 : p1.1 + p1.2 = s) (hs2 : p2.1 + p2.2 = s) (hs3 : p3.1 + p3.2 = s) :
    (((s, 0) : TrisectorLabel × TrisectorLabel) = p1 ∨ (s, 0) = p2 ∨ (s, 0) = p3) ∧
      (((s + 1, 2) : TrisectorLabel × TrisectorLabel) = p1 ∨ (s + 1, 2) = p2 ∨
        (s + 1, 2) = p3) ∧
      (((s + 2, 1) : TrisectorLabel × TrisectorLabel) = p1 ∨ (s + 2, 1) = p2 ∨
        (s + 2, 1) = p3) := by
  revert h12 h13 h23 hs1 hs2 hs3
  revert p1 p2 p3 s
  decide

/-- The two monochrome sides through the vertex `(s,0)` of the sum class `s` are parallel to
different Morley sides, for every colour. -/
theorem m3_class_sides (T : OrientedTriangle E o) (cc : TrisectorColor) (s : TrisectorLabel) :
    ∃ d e : TrisectorLabel, d ≠ e ∧
      Parallel (m3pSide T d)
        (T.constellationPoint ⟨cc, s, 0⟩ - T.constellationPoint ⟨cc, s + 2, 1⟩) ∧
      Parallel (m3pSide T e)
        (T.constellationPoint ⟨cc, s + 1, 2⟩ - T.constellationPoint ⟨cc, s, 0⟩) := by
  cases cc
  · refine ⟨s, s + 2, ?_, m3p_red_par31 T s, m3p_red_par12 T s⟩
    intro h
    have h' : s + 0 = s + 2 := by rw [add_zero]; exact h
    exact absurd (add_left_cancel h') (by decide)
  · refine ⟨s + 1, s, ?_, m3p_green_par31 T s, m3p_green_par12 T s⟩
    intro h
    exact absurd (add_left_cancel (by rw [add_zero]; exact h : s + 1 = s + 0)) (by decide)
  · refine ⟨s + 2, s + 1, ?_, m3p_blue_par31 T s, m3p_blue_par12 T s⟩
    intro h
    exact absurd (add_left_cancel h) (by decide)

/-- **No third point of a colour on a side-parallel line**, given two points of that colour
which form an equal-sum, non-diagonal pair.  This is the per-line form of the "at most two of
each colour" bound; it uses only the non-diagonal exclusion `m3HPnd`. -/
theorem m3_no_third_nd (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) {ℓ : Line E} (hdir : T.parallelToMorleySide ℓ.direction)
    {cc : TrisectorColor} {p1 p2 r : TrisectorLabel × TrisectorLabel}
    (hne : p1 ≠ p2) (hnd : ¬ m3Diag p1 p2)
    (hsame : p1.1 + p1.2 = p2.1 + p2.2)
    (hm1 : ℓ.mem (T.constellationPoint ⟨cc, p1.1, p1.2⟩))
    (hm2 : ℓ.mem (T.constellationPoint ⟨cc, p2.1, p2.2⟩))
    (hr : ℓ.mem (T.constellationPoint ⟨cc, r.1, r.2⟩))
    (hr1 : r ≠ p1) (hr2 : r ≠ p2) : False := by
  have hlab12 : p1 ≠ p2 := hne
  by_cases hsum : r.1 + r.2 = p1.1 + p1.2
  · -- all three sums equal: the three points are a monochrome triangle
    have hsum2 : r.1 + r.2 = p2.1 + p2.2 := by rw [hsum, hsame]
    have hlab1r : (⟨p1.1, p1.2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨r.1, r.2⟩ := by
      intro heq
      obtain ⟨hA, hB⟩ := Prod.mk.inj heq
      exact hr1 (by rw [Prod.ext_iff]; exact ⟨hA.symm, hB.symm⟩)
    have hlab2r : (⟨p2.1, p2.2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨r.1, r.2⟩ := by
      intro heq
      obtain ⟨hA, hB⟩ := Prod.mk.inj heq
      exact hr2 (by rw [Prod.ext_iff]; exact ⟨hA.symm, hB.symm⟩)
    set sv := p1.1 + p1.2 with hsv
    obtain ⟨d, e, hde, hpar1, hpar2⟩ := m3_class_sides T cc sv
    have hcov := m3_sumclass_cover ⟨p1.1, p1.2⟩ ⟨p2.1, p2.2⟩ ⟨r.1, r.2⟩ sv hlab12 hlab1r hlab2r
      (by rw [hsv]) (by rw [hsv]; exact hsame.symm) (by rw [hsv]; exact hsum)
    have key : ∀ x y : TrisectorLabel,
        (((x, y) : TrisectorLabel × TrisectorLabel) = ⟨p1.1, p1.2⟩ ∨
          (x, y) = ⟨p2.1, p2.2⟩ ∨ (x, y) = ⟨r.1, r.2⟩) →
        ℓ.mem (T.constellationPoint ⟨cc, x, y⟩) := by
      rintro x y (h | h | h)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hm1
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hm2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hr
    have hmem0 : ℓ.mem (T.constellationPoint ⟨cc, sv, 0⟩) := key sv 0 hcov.1
    have hmem12 : ℓ.mem (T.constellationPoint ⟨cc, sv + 1, 2⟩) := key (sv + 1) 2 hcov.2.1
    have hmem21 : ℓ.mem (T.constellationPoint ⟨cc, sv + 2, 1⟩) := key (sv + 2) 1 hcov.2.2
    have j1 : Parallel ℓ.direction
        (T.constellationPoint ⟨cc, sv, 0⟩ - T.constellationPoint ⟨cc, sv + 2, 1⟩) :=
      Line.parallel_of_mem_sub hmem21 hmem0
    have j2 : Parallel ℓ.direction
        (T.constellationPoint ⟨cc, sv + 1, 2⟩ - T.constellationPoint ⟨cc, sv, 0⟩) :=
      Line.parallel_of_mem_sub hmem0 hmem12
    have hne1 : T.constellationPoint ⟨cc, sv, 0⟩ -
        T.constellationPoint ⟨cc, sv + 2, 1⟩ ≠ 0 := by
      intro h0
      have hp : T.constellationPoint ⟨cc, sv, 0⟩ =
          T.constellationPoint ⟨cc, sv + 2, 1⟩ := sub_eq_zero.mp h0
      have hsec : (0 : TrisectorLabel) = 1 := congrArg ConstellationIndex.second (h hp)
      exact absurd hsec (by decide)
    have hne2 : T.constellationPoint ⟨cc, sv + 1, 2⟩ -
        T.constellationPoint ⟨cc, sv, 0⟩ ≠ 0 := by
      intro h0
      have hp : T.constellationPoint ⟨cc, sv + 1, 2⟩ =
          T.constellationPoint ⟨cc, sv, 0⟩ := sub_eq_zero.mp h0
      have hsec : (2 : TrisectorLabel) = 0 := congrArg ConstellationIndex.second (h hp)
      exact absurd hsec (by decide)
    exact m3_sides_ne_par T hde
      (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero
        (m4_parallel_of_parallel_of_parallel hne1 hpar1 j1)
        (m4_parallel_of_parallel_of_parallel hne2 hpar2 j2))
  · -- `r` has a different sum from `p1` and `p2`; one of the two pairs is non-diagonal
    have hsum2 : r.1 + r.2 ≠ p2.1 + p2.2 := by rw [← hsame]; exact hsum
    obtain ⟨d, hd⟩ := m3_exists_side T hdir
    by_cases hd1 : m3Diag r p1
    · -- then `r` and `p2` are NOT diagonal, since `p1`,`p2` are not
      have hnd2 : ¬ m3Diag r p2 := by
        intro hd2
        refine hnd ?_
        have h1' : r.2 - r.1 = p1.2 - p1.1 := hd1
        have h2' : r.2 - r.1 = p2.2 - p2.1 := hd2
        show p1.2 - p1.1 = p2.2 - p2.1
        rw [← h1', h2']
      exact HPnd cc r p2 hr2 hsum2 hnd2 d
        (m3_par_trans hd (Line.parallel_of_mem_sub hr hm2))
    · exact HPnd cc r p1 hr1 hsum hd1 d
        (m3_par_trans hd (Line.parallel_of_mem_sub hr hm1))

/-- Exactly two points of a colour lie on a side-parallel line, given two of them forming an
equal-sum non-diagonal pair. -/
theorem m3_colour_two_nd (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (HPnd : m3HPnd T) {ℓ : Line E} (hdir : T.parallelToMorleySide ℓ.direction)
    {cc : TrisectorColor} {p1 p2 : TrisectorLabel × TrisectorLabel}
    (hne : p1 ≠ p2) (hnd : ¬ m3Diag p1 p2) (hsame : p1.1 + p1.2 = p2.1 + p2.2)
    (hm1 : ℓ.mem (T.constellationPoint ⟨cc, p1.1, p1.2⟩))
    (hm2 : ℓ.mem (T.constellationPoint ⟨cc, p2.1, p2.2⟩)) :
    {q : ConstellationIndex | q.color = cc ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2 := by
  classical
  have hsub : {q : ConstellationIndex | q.color = cc ∧ ℓ.mem (T.constellationPoint q)} ⊆
      ({⟨cc, p1.1, p1.2⟩, ⟨cc, p2.1, p2.2⟩} : Set ConstellationIndex) := by
    intro q hq
    obtain ⟨qc, qa, qb⟩ := q
    simp only [Set.mem_ofPred_eq] at hq
    obtain ⟨hcq, hmem⟩ := hq
    rw [hcq] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hnot
    push_neg at hnot
    obtain ⟨h1, h2⟩ := hnot
    refine m3_no_third_nd T h HPnd hdir (cc := cc) (p1 := p1) (p2 := p2) (r := ⟨qa, qb⟩)
      hne hnd hsame hm1 hm2 hmem ?_ ?_
    · intro heq
      refine h1 ?_
      have hA : qa = p1.1 := congrArg Prod.fst heq
      have hB : qb = p1.2 := congrArg Prod.snd heq
      rw [hA, hB, hcq]
    · intro heq
      refine h2 ?_
      have hA : qa = p2.1 := congrArg Prod.fst heq
      have hB : qb = p2.2 := congrArg Prod.snd heq
      rw [hA, hB, hcq]
  have h2 : {q : ConstellationIndex | q.color = cc ∧ ℓ.mem (T.constellationPoint q)}.ncard ≤ 2 := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_insert_of_notMem _ , Set.ncard_singleton] at this
    intro heq
    exact hne (by
      have hf : (⟨p1.1, p1.2⟩ : TrisectorLabel × TrisectorLabel) = ⟨p2.1, p2.2⟩ :=
        Prod.ext (congrArg ConstellationIndex.first heq) (congrArg ConstellationIndex.second heq)
      exact hf)
  have hge : 2 ≤ {q : ConstellationIndex | q.color = cc ∧ ℓ.mem (T.constellationPoint q)}.ncard := by
    have hsub2 : ({⟨cc, p1.1, p1.2⟩, ⟨cc, p2.1, p2.2⟩} : Set ConstellationIndex) ⊆
        {q : ConstellationIndex | q.color = cc ∧ ℓ.mem (T.constellationPoint q)} := by
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact ⟨rfl, hm1⟩
      · exact ⟨rfl, hm2⟩
    have hpair : ({⟨cc, p1.1, p1.2⟩, ⟨cc, p2.1, p2.2⟩} : Set ConstellationIndex).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_singleton_iff]
        intro heq
        exact hne (by
          have hf : (⟨p1.1, p1.2⟩ : TrisectorLabel × TrisectorLabel) = ⟨p2.1, p2.2⟩ :=
            Prod.ext (congrArg ConstellationIndex.first heq) (congrArg ConstellationIndex.second heq)
          exact hf)), Set.ncard_singleton]
    rw [← hpair]
    exact Set.ncard_le_ncard hsub2 (Set.toFinite _)
  omega

/-- Two of the nine lines are different as soon as the line through one of their points is
side-parallel and the two points form a non-diagonal unequal-sum pair. -/
theorem m3_ne_of_nd_pair (T : OrientedTriangle E o) (HPnd : m3HPnd T)
    {ℓ ℓ' : Line E} (hdir : T.parallelToMorleySide ℓ.direction)
    {cc : TrisectorColor} {p q : TrisectorLabel × TrisectorLabel}
    (hne : p ≠ q) (hsum : p.1 + p.2 ≠ q.1 + q.2) (hnd : ¬ m3Diag p q)
    (hp : ℓ.mem (T.constellationPoint ⟨cc, p.1, p.2⟩))
    (hq : ℓ'.mem (T.constellationPoint ⟨cc, q.1, q.2⟩)) : ℓ ≠ ℓ' := by
  rintro rfl
  obtain ⟨d, hd⟩ := m3_exists_side T hdir
  exact HPnd cc p q hne hsum hnd d
    (m3_par_trans hd (Line.parallel_of_mem_sub hp hq))

/-- **`hclass` from the two exclusion hypotheses**: on a guide line, two red constellation
points always have equal label sums. -/
theorem m3_hclass_of_exc (T : OrientedTriangle E o) (HPnd : m3HPnd T) (HD : m3DiagExc T) :
    ∀ (ℓ : Line E), ℓ ∈ T.guideLines → ∀ p q : TrisectorLabel × TrisectorLabel,
      ℓ.mem (T.m5_redPt p) → ℓ.mem (T.m5_redPt q) → p.1 + p.2 = q.1 + q.2 := by
  intro ℓ hℓ p q hp hq
  by_contra hne
  obtain ⟨d, hd⟩ := m3_exists_side T hℓ.1.1
  have hpq : p ≠ q := by
    rintro rfl
    exact hne rfl
  have hpar : Parallel (m3pSide T d) (T.m5_redPt q - T.m5_redPt p) :=
    m3_par_trans hd (Line.parallel_of_mem_sub hp hq)
  by_cases hdiag : m3Diag p q
  · exact HD p q hpq hdiag ℓ hℓ ⟨hp, hq⟩
  · exact HPnd .red p q hpq hne hdiag d hpar

end OrientedTriangle
end XamboMorley
