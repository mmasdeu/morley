import XamboMorleyBase

/-!
# m8 (swarm smwh7aexl) — assembly of the three guide-line count principals

This file is *additive*: the root `XamboMorley.lean` is imported, never modified.
Nothing here is a `sorry`, an `admit` or a new axiom; every declaration is checked in
`m8_axcheck.lean` with `#print axioms`.

## What is proved here

The root leaves three guide-line counting statements as `sorry`:

* `guideLines_card`           : `T.guideLines.ncard = 9`
* `point_on_two_guideLines`   : every constellation point lies on exactly two guide lines
* `guideLines_direction_card` : exactly three guide lines in each Morley side direction

They are derived here — statements reproduced verbatim, under the root's names inside
namespace `M8` — from exactly two hypotheses:

* `M8.ClassHyp T`: for every guide line `ℓ`, every colour `c` and all label pairs `p q`,
  incidence of both `c`-points on `ℓ` forces `p.1 + p.2 = q.1 + q.2` (equal label sums).
  The red case is the hypothesis of the root's `m5_ncard_le_nine`;
  `.ultramath/smwh4hpq8/m5` reduces it to nine concrete exclusions (one per pair of a
  label diagonal class) and `.ultramath/smwh1zs5u/m8/W8g.lean` transports the red case to
  the other two colours cyclically.
* `M8.DirHyp T`: in each of the three Morley side directions there are at least three
  pairwise distinct guide lines (the constructive half; the 54 incidences of the nine
  equal-sum joins are compiled in `.ultramath/smwh1zs5u/m2/M2P.lean`; what is still
  missing for it is exactness `ncard = 6` of those joins).

Both are *true* statements about the Xambo–Morley configuration; in particular
`ClassHyp` is strictly weaker than the "broad HP" form ("no unequal-sum same-colour join
is parallel to a Morley side"), which is false — see
`.ultramath/smwh4hpq8/m5/README.md`.

The content of the file is double counting. `DirHyp` produces nine distinct guide lines
without assuming any direction count, so `9 ≤ |guideLines|`; `ClassHyp` bounds the number
of guide lines through a constellation point by the two equal-sum partners of its label
(distinct guide lines through the point give distinct partners), so `|guideLines| ≤ 9`;
finally the nine lines split into three direction classes that cover `guideLines`, and
each class contains the three lines supplied by `DirHyp`, so each class has exactly three
members.
-/

noncomputable section

open scoped Real RealInnerProductSpace
open Function Set

namespace XamboMorley
namespace OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-- The constellation point of colour `c` with label pair `p` (helper of member m8). -/
def m8cp (T : OrientedTriangle E o) (c : TrisectorColor)
    (p : TrisectorLabel × TrisectorLabel) : E :=
  T.constellationPoint ⟨c, p.1, p.2⟩

namespace M8

open XamboMorley.OrientedTriangle.OrientedTriangle

/-! ## 1. Constellation points by colour and label pair -/

theorem cp_red (T : OrientedTriangle E o) (p : TrisectorLabel × TrisectorLabel) :
    m8cp T .red p = T.m5_redPt p := rfl

/-- Equal constellation points have equal colour and equal labels. -/
theorem cp_inj (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {c c' : TrisectorColor} {p p' : TrisectorLabel × TrisectorLabel}
    (he : m8cp T c p = m8cp T c' p') : c = c' ∧ p = p' := by
  have hidx : (⟨c, p.1, p.2⟩ : ConstellationIndex) = ⟨c', p'.1, p'.2⟩ := h he
  refine ⟨?_, ?_⟩
  · simpa using congrArg ConstellationIndex.color hidx
  · have h1 : p.1 = p'.1 := by simpa using congrArg ConstellationIndex.first hidx
    have h2 : p.2 = p'.2 := by simpa using congrArg ConstellationIndex.second hidx
    exact Prod.ext h1 h2

theorem cp_ne (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {c : TrisectorColor} {p p' : TrisectorLabel × TrisectorLabel} (hp : p ≠ p') :
    m8cp T c p ≠ m8cp T c p' :=
  fun he => hp (cp_inj T h he).2

/-- Rebuilding a constellation index from its colour and labels. -/
theorem cp_index (T : OrientedTriangle E o) (q : ConstellationIndex) :
    m8cp T q.color (q.first, q.second) = T.constellationPoint q := by
  obtain ⟨c, a, b⟩ := q
  rfl

/-! ## 2. `IsGuideLine` in terms of the three per-colour counts -/

/-- The six-point condition follows from the three two-point conditions. -/
theorem ncard_six_of_colour_counts (T : OrientedTriangle E o) (ℓ : Line E)
    (h : ∀ c : TrisectorColor,
      {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2) :
    {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)}.ncard = 6 := by
  classical
  set A : TrisectorColor → Set ConstellationIndex :=
    fun c => {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)}
    with hA
  have hdisj : ∀ c c' : TrisectorColor, c ≠ c' → Disjoint (A c) (A c') := by
    intro c c' hne
    rw [Set.disjoint_left]
    rintro q ⟨hq, -⟩ ⟨hq', -⟩
    exact hne (hq.symm.trans hq')
  have hpart : {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)} =
      ((A .red ∪ A .green) ∪ A .blue) := by
    ext q
    constructor
    · intro hq
      rcases q with ⟨c, i, j⟩
      cases c
      · exact Or.inl (Or.inl ⟨rfl, hq⟩)
      · exact Or.inl (Or.inr ⟨rfl, hq⟩)
      · exact Or.inr ⟨rfl, hq⟩
    · rintro ((⟨-, hq⟩ | ⟨-, hq⟩) | ⟨-, hq⟩)
      · exact hq
      · exact hq
      · exact hq
  have hd1 : Disjoint (A .red ∪ A .green) (A .blue) := by
    rw [Set.disjoint_left]
    rintro q (hq | hq) hq'
    · exact Set.disjoint_left.mp (hdisj _ _ (by decide : TrisectorColor.red ≠ TrisectorColor.blue)) hq hq'
    · exact Set.disjoint_left.mp (hdisj _ _ (by decide : TrisectorColor.green ≠ TrisectorColor.blue)) hq hq'
  have hd0 : Disjoint (A .red) (A .green) := hdisj _ _ (by decide)
  have hf : ∀ c, (A c).Finite := fun c => Set.toFinite _
  rw [hpart, m4_ncard_union_of_disjoint ((hf _).union (hf _)) (hf _) hd1,
    m4_ncard_union_of_disjoint (hf _) (hf _) hd0, h .red, h .green, h .blue]

/-- **`IsGuideLine` is "Morley-side parallel and two points of every colour"**: the
`ncard = 6` clause of the root definition is redundant. -/
theorem isGuideLine_iff (T : OrientedTriangle E o) (ℓ : Line E) :
    T.IsGuideLine ℓ ↔ T.parallelToMorleySide ℓ.direction ∧
      ∀ c : TrisectorColor,
        {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2 := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ncard_six_of_colour_counts T ℓ h2, h2⟩

/-- A guide line carries exactly two constellation points of the colour `c`. -/
theorem guide_two (T : OrientedTriangle E o) {ℓ : Line E} (hℓ : ℓ ∈ T.guideLines)
    (c : TrisectorColor) :
    {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)}.ncard = 2 :=
  hℓ.1.2.2 c

/-- A guide line carries no three distinct points of one colour. -/
theorem guide_not_three (T : OrientedTriangle E o) {ℓ : Line E} (hℓ : ℓ ∈ T.guideLines)
    (c : TrisectorColor) {q₁ q₂ q₃ : ConstellationIndex}
    (h1 : q₁.color = c) (h2 : q₂.color = c) (h3 : q₃.color = c)
    (hm1 : ℓ.mem (T.constellationPoint q₁)) (hm2 : ℓ.mem (T.constellationPoint q₂))
    (hm3 : ℓ.mem (T.constellationPoint q₃)) (d12 : q₁ ≠ q₂) (d13 : q₁ ≠ q₃)
    (d23 : q₂ ≠ q₃) : False := by
  have hsub : ({q₁, q₂, q₃} : Set ConstellationIndex) ⊆
      {q : ConstellationIndex | q.color = c ∧ ℓ.mem (T.constellationPoint q)} := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨h1, hm1⟩
    · exact ⟨h2, hm2⟩
    · exact ⟨h3, hm3⟩
  have h3c : ({q₁, q₂, q₃} : Set ConstellationIndex).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [d12, d13]),
      Set.ncard_insert_of_notMem (by simp [d23]), Set.ncard_singleton]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3c, guide_two T hℓ c] at this
  omega

/-! ## 3. The three Morley side directions are pairwise non-parallel -/

theorem m3pSide_ne_zero (T : OrientedTriangle E o) (d : TrisectorLabel) :
    m3pSide T d ≠ 0 := by
  rcases zmod3_cases d with hd | hd | hd
  · rw [hd, m3p_side_zero]; exact T.m2_Y_sub_X_ne
  · rw [hd, m3p_side_one]; exact T.m2_Z_sub_Y_ne
  · rw [hd, m3p_side_two]
    intro hzero
    have hd0 : dist T.Z T.X = 0 := by
      rw [dist_eq_norm, show T.Z - T.X = -(T.X - T.Z) from by abel, hzero, neg_zero,
        norm_zero]
    have hpos : 0 < dist T.Z T.X := by
      rw [T.morley_side_lengths.2.2]
      have h1 := m7_delta_pos T; have h2 := m7_sin_alpha_pos T
      have h3 := m7_sin_beta_pos T; have h4 := m7_sin_gamma_pos T
      positivity
    linarith

theorem m3pSide_not_parallel (T : OrientedTriangle E o) {d d' : TrisectorLabel}
    (h : d ≠ d') : ¬ Parallel (m3pSide T d) (m3pSide T d') := by
  have hn := T.m4_not_parallel_morley
  rcases zmod3_cases d with hd | hd | hd <;> rcases zmod3_cases d' with hd' | hd' | hd'
  · exact absurd (hd.trans hd'.symm) h
  · rw [hd, hd', m3p_side_zero, m3p_side_one]; exact hn.1
  · rw [hd, hd', m3p_side_zero, m3p_side_two]
    exact fun hc => hn.2.2 (parallel_comm (m3pSide_ne_zero T 0) (m3pSide_ne_zero T 2) hc)
  · rw [hd, hd', m3p_side_one, m3p_side_zero]
    exact fun hc => hn.1 (parallel_comm (m3pSide_ne_zero T 1) (m3pSide_ne_zero T 0) hc)
  · exact absurd (hd.trans hd'.symm) h
  · rw [hd, hd', m3p_side_one, m3p_side_two]; exact hn.2.1
  · rw [hd, hd', m3p_side_two, m3p_side_zero]; exact hn.2.2
  · rw [hd, hd', m3p_side_two, m3p_side_one]
    exact fun hc => hn.2.1 (parallel_comm (m3pSide_ne_zero T 2) (m3pSide_ne_zero T 1) hc)
  · exact absurd (hd.trans hd'.symm) h

/-! ## 4. The two residual hypotheses -/

/-- **Classification hypothesis**: two constellation points of one colour on a guide line
have equal label sums. -/
def ClassHyp (T : OrientedTriangle E o) : Prop :=
  ∀ (c : TrisectorColor) (ℓ : Line E), ℓ ∈ T.guideLines →
    ∀ p q : TrisectorLabel × TrisectorLabel,
      ℓ.mem (m8cp T c p) → ℓ.mem (m8cp T c q) → p.1 + p.2 = q.1 + q.2

/-- **Constructive hypothesis**: in every Morley side direction there are three pairwise
distinct guide lines, as an injective family indexed by `ZMod 3`. -/
def DirHyp (T : OrientedTriangle E o) : Prop :=
  ∀ d : TrisectorLabel, ∃ f : TrisectorLabel → Line E,
    (∀ s, f s ∈ T.guideLines) ∧ Injective f ∧
      ∀ s, Parallel (m3pSide T d) (f s).direction

/-! ## 5. Upper bound: at most nine guide lines -/

/-- The red case of `ClassHyp`, in the shape the root's `m5_ncard_le_nine` expects. -/
theorem classHyp_red (T : OrientedTriangle E o) (hC : ClassHyp T) :
    ∀ (ℓ : Line E), ℓ ∈ T.guideLines → ∀ p q : TrisectorLabel × TrisectorLabel,
      ℓ.mem (T.m5_redPt p) → ℓ.mem (T.m5_redPt q) → p.1 + p.2 = q.1 + q.2 := by
  intro ℓ hℓ p q hp hq
  exact hC .red ℓ hℓ p q (by rw [cp_red]; exact hp) (by rw [cp_red]; exact hq)


/-! ### `decide` replacements for the root's three `native_decide` counts

The root proves `equalSumPair_ordered_ncard` and `equalSumPair_partners` by
`native_decide`, which introduces a `native_decide` axiom.  The same computations go
through with plain `decide`, so the chain below depends only on `propext`,
`Classical.choice` and `Quot.sound`. -/

theorem m8_ordered_ncard :
    {r : (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) |
      r.1 ≠ r.2 ∧ r.1.1 + r.1.2 = r.2.1 + r.2.2}.ncard = 18 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  decide

theorem m8_partners (p : TrisectorLabel × TrisectorLabel) :
    {q : TrisectorLabel × TrisectorLabel | p ≠ q ∧ p.1 + p.2 = q.1 + q.2}.ncard = 2 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  revert p
  decide

theorem m8_direction_ncard (d : TrisectorLabel) :
    {r : (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) |
      r.1 ≠ r.2 ∧ r.1.1 + r.1.2 = r.2.1 + r.2.2 ∧ pairDirection r.1 r.2 = d}.ncard = 6 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  revert d
  decide

/-- The root's `m5_ncard_le_nine`, reproved against the `decide` count so that no
`native_decide` axiom is used. -/
theorem ncard_le_nine_clean (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hclass : ∀ (ℓ : Line E), ℓ ∈ T.guideLines → ∀ p q : TrisectorLabel × TrisectorLabel,
      ℓ.mem (T.m5_redPt p) → ℓ.mem (T.m5_redPt q) → p.1 + p.2 = q.1 + q.2) :
    T.guideLines.ncard ≤ 9 := by
  classical
  set G := T.guideLines with hG
  have hex : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, ∃ q₁ q₂ : ConstellationIndex, q₁ ≠ q₂ ∧
      {q : ConstellationIndex | q.color = .red ∧ (ℓ : Line E).mem (T.constellationPoint q)}
        = {q₁, q₂} := by
    intro ℓ
    exact Set.ncard_eq_two.mp (ℓ.2.1.2.2 TrisectorColor.red)
  choose f₁ f₂ hf using hex
  have hmem₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (f₁ ℓ).color = .red ∧ (ℓ : Line E).mem (T.constellationPoint (f₁ ℓ)) := by
    intro ℓ
    have hins : f₁ ℓ ∈ {q : ConstellationIndex |
        q.color = .red ∧ (ℓ : Line E).mem (T.constellationPoint q)} := by
      rw [(hf ℓ).2]; exact Set.mem_insert _ _
    exact hins
  have hmem₂ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (f₂ ℓ).color = .red ∧ (ℓ : Line E).mem (T.constellationPoint (f₂ ℓ)) := by
    intro ℓ
    have hins : f₂ ℓ ∈ {q : ConstellationIndex |
        q.color = .red ∧ (ℓ : Line E).mem (T.constellationPoint q)} := by
      rw [(hf ℓ).2]; exact Set.mem_insert_of_mem _ rfl
    exact hins
  have hlab : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, ((f₁ ℓ).first, (f₁ ℓ).second) ≠ ((f₂ ℓ).first, (f₂ ℓ).second) := by
    intro ℓ heq
    have h1 : (f₁ ℓ).first = (f₂ ℓ).first := congrArg Prod.fst heq
    have h2 : (f₁ ℓ).second = (f₂ ℓ).second := congrArg Prod.snd heq
    have hc : (f₁ ℓ).color = (f₂ ℓ).color := by rw [(hmem₁ ℓ).1, (hmem₂ ℓ).1]
    exact (hf ℓ).1 (m5_ci_ext hc h1 h2)
  have hpt : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      T.constellationPoint (f₁ ℓ) ≠ T.constellationPoint (f₂ ℓ) := by
    intro ℓ hc
    exact (hf ℓ).1 (h hc)
  have hshared : ∀ ℓ ℓ' : {ℓ : Line E // ℓ ∈ G},
      (ℓ : Line E).mem (T.constellationPoint (f₁ ℓ)) →
      (ℓ : Line E).mem (T.constellationPoint (f₂ ℓ)) →
      (ℓ' : Line E).mem (T.constellationPoint (f₁ ℓ)) →
      (ℓ' : Line E).mem (T.constellationPoint (f₂ ℓ)) → ℓ = ℓ' := by
    intro ℓ ℓ' h1 h2 h3 h4
    have hiff := m4_mem_iff_of_two_mem (hpt ℓ) h1 h2 h3 h4
    exact Subtype.ext (isCanonical_eq_of_mem_iff ℓ.2.2 ℓ'.2.2 hiff)
  let P₀ : {ℓ : Line E // ℓ ∈ G} →
      (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) :=
    fun ℓ => (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second))
  let P₁ : {ℓ : Line E // ℓ ∈ G} →
      (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) :=
    fun ℓ => (((f₂ ℓ).first, (f₂ ℓ).second), ((f₁ ℓ).first, (f₁ ℓ).second))
  have hval₀ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (ℓ : Line E).mem (T.m5_redPt (P₀ ℓ).1) ∧ (ℓ : Line E).mem (T.m5_redPt (P₀ ℓ).2) := by
    intro ℓ
    refine ⟨?_, ?_⟩
    · show (ℓ : Line E).mem (T.m5_redPt ((f₁ ℓ).first, (f₁ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₁ ℓ).1]
      exact (hmem₁ ℓ).2
    · show (ℓ : Line E).mem (T.m5_redPt ((f₂ ℓ).first, (f₂ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₂ ℓ).1]
      exact (hmem₂ ℓ).2
  have hval₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G},
      (ℓ : Line E).mem (T.m5_redPt (P₁ ℓ).1) ∧ (ℓ : Line E).mem (T.m5_redPt (P₁ ℓ).2) := by
    intro ℓ
    refine ⟨?_, ?_⟩
    · show (ℓ : Line E).mem (T.m5_redPt ((f₂ ℓ).first, (f₂ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₂ ℓ).1]
      exact (hmem₂ ℓ).2
    · show (ℓ : Line E).mem (T.m5_redPt ((f₁ ℓ).first, (f₁ ℓ).second))
      rw [m5_mem_redPt_of_mem (hmem₁ ℓ).1]
      exact (hmem₁ ℓ).2
  have heq₀ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, P₀ ℓ = (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second)) := fun ℓ => rfl
  have heq₁ : ∀ ℓ : {ℓ : Line E // ℓ ∈ G}, P₁ ℓ = (((f₂ ℓ).first, (f₂ ℓ).second), ((f₁ ℓ).first, (f₁ ℓ).second)) := fun ℓ => rfl
  have hP₀inj : Function.Injective P₀ := by
    intro ℓ ℓ' heq
    have he : (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second)) =
        (((f₁ ℓ').first, (f₁ ℓ').second), ((f₂ ℓ').first, (f₂ ℓ').second)) := by
      rw [← heq₀ ℓ, ← heq₀ ℓ']; exact heq
    have h1 : ((f₁ ℓ).first, (f₁ ℓ).second) = ((f₁ ℓ').first, (f₁ ℓ').second) := congrArg Prod.fst he
    have h2 : ((f₂ ℓ).first, (f₂ ℓ).second) = ((f₂ ℓ').first, (f₂ ℓ').second) := congrArg Prod.snd he
    have e1 : T.constellationPoint (f₁ ℓ) = T.constellationPoint (f₁ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₁ ℓ).1, ← m5_mem_redPt_of_mem (hmem₁ ℓ').1, h1]
    have e2 : T.constellationPoint (f₂ ℓ) = T.constellationPoint (f₂ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₂ ℓ).1, ← m5_mem_redPt_of_mem (hmem₂ ℓ').1, h2]
    exact hshared ℓ ℓ' (hmem₁ ℓ).2 (hmem₂ ℓ).2 (e1 ▸ (hmem₁ ℓ').2) (e2 ▸ (hmem₂ ℓ').2)
  have hP₁inj : Function.Injective P₁ := by
    intro ℓ ℓ' heq
    have he : (((f₂ ℓ).first, (f₂ ℓ).second), ((f₁ ℓ).first, (f₁ ℓ).second)) =
        (((f₂ ℓ').first, (f₂ ℓ').second), ((f₁ ℓ').first, (f₁ ℓ').second)) := by
      rw [← heq₁ ℓ, ← heq₁ ℓ']; exact heq
    have h1 : ((f₂ ℓ).first, (f₂ ℓ).second) = ((f₂ ℓ').first, (f₂ ℓ').second) := congrArg Prod.fst he
    have h2 : ((f₁ ℓ).first, (f₁ ℓ).second) = ((f₁ ℓ').first, (f₁ ℓ').second) := congrArg Prod.snd he
    have e1 : T.constellationPoint (f₂ ℓ) = T.constellationPoint (f₂ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₂ ℓ).1, ← m5_mem_redPt_of_mem (hmem₂ ℓ').1, h1]
    have e2 : T.constellationPoint (f₁ ℓ) = T.constellationPoint (f₁ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₁ ℓ).1, ← m5_mem_redPt_of_mem (hmem₁ ℓ').1, h2]
    exact hshared ℓ ℓ' (hmem₁ ℓ).2 (hmem₂ ℓ).2 (e2 ▸ (hmem₁ ℓ').2) (e1 ▸ (hmem₂ ℓ').2)
  have hdisj : Disjoint (P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}))
      (P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})) := by
    rw [Set.disjoint_left]
    rintro p hp₀ hp₁
    obtain ⟨ℓ, -, rfl⟩ := hp₀
    obtain ⟨ℓ', -, heq⟩ := hp₁
    have he : (((f₁ ℓ).first, (f₁ ℓ).second), ((f₂ ℓ).first, (f₂ ℓ).second)) =
        (((f₂ ℓ').first, (f₂ ℓ').second), ((f₁ ℓ').first, (f₁ ℓ').second)) := by
      rw [← heq₀ ℓ, ← heq₁ ℓ']; exact heq.symm
    have h1 : ((f₁ ℓ).first, (f₁ ℓ).second) = ((f₂ ℓ').first, (f₂ ℓ').second) := congrArg Prod.fst he
    have h2 : ((f₂ ℓ).first, (f₂ ℓ).second) = ((f₁ ℓ').first, (f₁ ℓ').second) := congrArg Prod.snd he
    have e1 : T.constellationPoint (f₁ ℓ) = T.constellationPoint (f₂ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₁ ℓ).1, ← m5_mem_redPt_of_mem (hmem₂ ℓ').1, h1]
    have e2 : T.constellationPoint (f₂ ℓ) = T.constellationPoint (f₁ ℓ') := by
      rw [← m5_mem_redPt_of_mem (hmem₂ ℓ).1, ← m5_mem_redPt_of_mem (hmem₁ ℓ').1, h2]
    have hll : ℓ = ℓ' := hshared ℓ ℓ' (hmem₁ ℓ).2 (hmem₂ ℓ).2
      (e1 ▸ (hmem₂ ℓ').2) (e2 ▸ (hmem₁ ℓ').2)
    subst hll
    exact hlab ℓ h1
  have hsub : (P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}) ∪
      P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})) ⊆
      {r : (TrisectorLabel × TrisectorLabel) × (TrisectorLabel × TrisectorLabel) |
        r.1 ≠ r.2 ∧ r.1.1 + r.1.2 = r.2.1 + r.2.2} := by
    rintro _ (hp | hp)
    · obtain ⟨ℓ, -, rfl⟩ := hp
      have hv := hval₀ ℓ
      exact ⟨hlab ℓ, hclass ℓ.1 ℓ.2 _ _ hv.1 hv.2⟩
    · obtain ⟨ℓ, -, rfl⟩ := hp
      have hv := hval₁ ℓ
      exact ⟨fun hc => hlab ℓ hc.symm, (hclass ℓ.1 ℓ.2 _ _ hv.2 hv.1).symm⟩
  have hI₀ : (P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})).ncard = G.ncard := by
    rw [Set.ncard_image_of_injective _ hP₀inj, Set.ncard_univ, ← Nat.card_coe_set_eq]
  have hI₁ : (P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G})).ncard = G.ncard := by
    rw [Set.ncard_image_of_injective _ hP₁inj, Set.ncard_univ, ← Nat.card_coe_set_eq]
  have hunion : ((P₀ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}) ∪
      P₁ '' (Set.univ : Set {ℓ : Line E // ℓ ∈ G}))).ncard = G.ncard + G.ncard := by
    rw [m4_ncard_union_of_disjoint (Set.toFinite _) (Set.toFinite _) hdisj, hI₀, hI₁]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hunion, m8_ordered_ncard] at hle
  rw [hG] at hle ⊢
  omega




theorem ncard_le_nine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hC : ClassHyp T) : T.guideLines.ncard ≤ 9 :=
  ncard_le_nine_clean T h (classHyp_red T hC)

/-! ## 6. At most two guide lines through a constellation point -/

/-- The second point of colour `c` on a guide line through `m8cp T c p` has the same label
sum as `p`. -/
theorem exists_partner (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hC : ClassHyp T) (c : TrisectorColor) (p : TrisectorLabel × TrisectorLabel)
    {ℓ : Line E} (hℓ : ℓ ∈ T.guideLines) (hp : ℓ.mem (m8cp T c p)) :
    ∃ r : TrisectorLabel × TrisectorLabel, p ≠ r ∧ p.1 + p.2 = r.1 + r.2 ∧
      m8cp T c r ≠ m8cp T c p ∧ ℓ.mem (m8cp T c r) := by
  classical
  set A : Set ConstellationIndex :=
    {q | q.color = c ∧ ℓ.mem (T.constellationPoint q)} with hA
  have hA2 : A.ncard = 2 := hℓ.1.2.2 c
  obtain ⟨q₁, q₂, hne, hAeq⟩ := Set.ncard_eq_two.mp hA2
  have hpA : (⟨c, p.1, p.2⟩ : ConstellationIndex) ∈ A := ⟨rfl, hp⟩
  rw [hAeq] at hpA
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpA
  have hex : ∃ q ∈ A, q ≠ (⟨c, p.1, p.2⟩ : ConstellationIndex) := by
    rcases hpA with h1 | h2
    · exact ⟨q₂, by rw [hAeq]; exact Set.mem_insert_of_mem _ rfl,
        fun hc => hne (by rw [← h1, ← hc])⟩
    · exact ⟨q₁, by rw [hAeq]; exact Set.mem_insert _ _,
        fun hc => hne (by rw [← h2, ← hc])⟩
  obtain ⟨q, hqA, hqne⟩ := hex
  obtain ⟨hqc, hqmem⟩ := hqA
  obtain ⟨cq, a', b'⟩ := q
  simp only at hqc hqmem hqne
  rw [hqc] at hqmem hqne
  clear hqc
  have hqne' : (⟨c, a', b'⟩ : ConstellationIndex) ≠ ⟨c, p.1, p.2⟩ := hqne
  have hpr : p ≠ (a', b') := by
    intro he
    exact hqne' (by rw [he])
  refine ⟨(a', b'), hpr, ?_, Ne.symm (cp_ne T h hpr), hqmem⟩
  exact hC c ℓ hℓ p (a', b') hp hqmem

/-- **`ClassHyp` gives at most two guide lines through any constellation point.** -/
theorem point_le_two (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hC : ClassHyp T) (c : TrisectorColor) (p : TrisectorLabel × TrisectorLabel) :
    {ℓ ∈ T.guideLines | ℓ.mem (m8cp T c p)}.ncard ≤ 2 := by
  classical
  have hex : ∀ ℓ : {ℓ ∈ T.guideLines | ℓ.mem (m8cp T c p)},
      ∃ r : TrisectorLabel × TrisectorLabel, p ≠ r ∧ p.1 + p.2 = r.1 + r.2 ∧
        m8cp T c r ≠ m8cp T c p ∧ (ℓ : Line E).mem (m8cp T c r) :=
    fun ℓ => exists_partner T h hC c p ℓ.2.1 ℓ.2.2
  choose f hf1 hf2 hf3 hf4 using hex
  have hinj : Function.Injective f := by
    intro ℓ ℓ' heq
    have hmem' : (ℓ' : Line E).mem (m8cp T c (f ℓ)) := by rw [heq]; exact hf4 ℓ'
    have hiff := m4_mem_iff_of_two_mem (Ne.symm (hf3 ℓ)) ℓ.2.2 (hf4 ℓ) ℓ'.2.2 hmem'
    exact Subtype.ext (isCanonical_eq_of_mem_iff ℓ.2.1.2 ℓ'.2.1.2 hiff)
  have hsub : Set.range f ⊆
      {q : TrisectorLabel × TrisectorLabel | p ≠ q ∧ p.1 + p.2 = q.1 + q.2} := by
    rintro _ ⟨ℓ, rfl⟩
    exact ⟨hf1 ℓ, hf2 ℓ⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcard : (Set.range f).ncard =
      {ℓ ∈ T.guideLines | ℓ.mem (m8cp T c p)}.ncard := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      ← Nat.card_coe_set_eq]
  rw [hcard, m8_partners p] at hle
  exact hle

/-- The same at index level. -/
theorem index_point_le_two (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hC : ClassHyp T) (q : ConstellationIndex) :
    {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard ≤ 2 := by
  obtain ⟨c, a, b⟩ := q
  have h' := point_le_two T h hC c (a, b)
  simpa only [m8cp] using h'

/-! ## 7. Lower bound: at least nine guide lines -/

theorem ncard_ge_nine (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hD : DirHyp T) : 9 ≤ T.guideLines.ncard := by
  classical
  choose f hfmem hfinj hfpar using hD
  set F : TrisectorLabel × TrisectorLabel → Line E := fun p => f p.1 p.2 with hF
  have hFinj : Function.Injective F := by
    rintro ⟨d, s⟩ ⟨d', s'⟩ he
    have he' : f d s = f d' s' := he
    by_cases hdd : d = d'
    · subst hdd
      have h1 : s = s' := hfinj d he'
      rw [h1]
    · refine absurd (m4_parallel_of_parallel_of_parallel (w := (f d s).direction)
        (f d s).direction_ne_zero (hfpar d s) ?_) (m3pSide_not_parallel T hdd)
      rw [he']
      exact hfpar d' s'
  have himg : (F '' (Set.univ : Set (TrisectorLabel × TrisectorLabel))).ncard = 9 := by
    rw [Set.ncard_image_of_injective _ hFinj, Set.ncard_univ, Nat.card_eq_fintype_card]
    simp [Fintype.card_prod, ZMod.card]
  have hsub : F '' (Set.univ : Set (TrisectorLabel × TrisectorLabel)) ⊆ T.guideLines := by
    rintro _ ⟨p, -, rfl⟩
    exact hfmem p.1 p.2
  calc (9 : ℕ) = (F '' Set.univ).ncard := himg.symm
    _ ≤ T.guideLines.ncard := Set.ncard_le_ncard hsub (m4_guideLines_finite T h)


/-! ## 8. The three direction classes of guide lines -/

/-- The guide lines parallel to `Y - X`. -/
def dirA (T : OrientedTriangle E o) : Set (Line E) :=
  {ℓ ∈ T.guideLines | Parallel (T.Y - T.X) ℓ.direction}

/-- The guide lines parallel to `Z - Y`. -/
def dirB (T : OrientedTriangle E o) : Set (Line E) :=
  {ℓ ∈ T.guideLines | Parallel (T.Z - T.Y) ℓ.direction}

/-- The guide lines parallel to `X - Z`. -/
def dirC (T : OrientedTriangle E o) : Set (Line E) :=
  {ℓ ∈ T.guideLines | Parallel (T.X - T.Z) ℓ.direction}

theorem mem_dirA {T : OrientedTriangle E o} {ℓ : Line E} :
    ℓ ∈ dirA T ↔ ℓ ∈ T.guideLines ∧ Parallel (T.Y - T.X) ℓ.direction := Iff.rfl

theorem mem_dirB {T : OrientedTriangle E o} {ℓ : Line E} :
    ℓ ∈ dirB T ↔ ℓ ∈ T.guideLines ∧ Parallel (T.Z - T.Y) ℓ.direction := Iff.rfl

theorem mem_dirC {T : OrientedTriangle E o} {ℓ : Line E} :
    ℓ ∈ dirC T ↔ ℓ ∈ T.guideLines ∧ Parallel (T.X - T.Z) ℓ.direction := Iff.rfl

/-- Every guide line lies in one of the three direction classes. -/
theorem guideLines_eq_union (T : OrientedTriangle E o) :
    T.guideLines = (dirA T ∪ dirB T) ∪ dirC T := by
  ext ℓ
  simp only [mem_dirA, mem_dirB, mem_dirC, Set.mem_union]
  constructor
  · intro h
    rcases (h.1.1 : T.parallelToMorleySide ℓ.direction) with h' | h' | h'
    · exact Or.inl (Or.inl ⟨h, h'⟩)
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr ⟨h, h'⟩
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h

theorem disjoint_dirAB (T : OrientedTriangle E o) : Disjoint (dirA T) (dirB T) := by
  rw [Set.disjoint_left]
  rintro ℓ ⟨-, hA⟩ ⟨-, hB⟩
  exact T.m4_not_parallel_morley.1
    (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hA hB)

theorem disjoint_dirAB_C (T : OrientedTriangle E o) :
    Disjoint (dirA T ∪ dirB T) (dirC T) := by
  rw [Set.disjoint_left]
  rintro ℓ (hAB | hAB) hC
  · exact T.m4_not_parallel_morley.2.2
      (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hC.2 hAB.2)
  · exact T.m4_not_parallel_morley.2.1
      (m4_parallel_of_parallel_of_parallel ℓ.direction_ne_zero hAB.2 hC.2)

/-- `DirHyp` supplies three guide lines parallel to `Y - X`. -/
theorem three_ge_dirA (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hD : DirHyp T) : 3 ≤ (dirA T).ncard := by
  classical
  obtain ⟨f, hmem, hinj, hpar⟩ := hD 0
  have himg : (f '' (Set.univ : Set TrisectorLabel)).ncard = 3 := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have hsub : f '' (Set.univ : Set TrisectorLabel) ⊆ dirA T := by
    rintro _ ⟨s, -, rfl⟩
    exact ⟨hmem s, by rw [← m3p_side_zero]; exact hpar s⟩
  calc (3 : ℕ) = (f '' Set.univ).ncard := himg.symm
    _ ≤ (dirA T).ncard :=
      Set.ncard_le_ncard hsub ((m4_guideLines_finite T h).subset (fun x hx => hx.1))

/-- `DirHyp` supplies three guide lines parallel to `Z - Y`. -/
theorem three_ge_dirB (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hD : DirHyp T) : 3 ≤ (dirB T).ncard := by
  classical
  obtain ⟨f, hmem, hinj, hpar⟩ := hD 1
  have himg : (f '' (Set.univ : Set TrisectorLabel)).ncard = 3 := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have hsub : f '' (Set.univ : Set TrisectorLabel) ⊆ dirB T := by
    rintro _ ⟨s, -, rfl⟩
    exact ⟨hmem s, by rw [← m3p_side_one]; exact hpar s⟩
  calc (3 : ℕ) = (f '' Set.univ).ncard := himg.symm
    _ ≤ (dirB T).ncard :=
      Set.ncard_le_ncard hsub ((m4_guideLines_finite T h).subset (fun x hx => hx.1))

/-- `DirHyp` supplies three guide lines parallel to `X - Z`. -/
theorem three_ge_dirC (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hD : DirHyp T) : 3 ≤ (dirC T).ncard := by
  classical
  obtain ⟨f, hmem, hinj, hpar⟩ := hD 2
  have himg : (f '' (Set.univ : Set TrisectorLabel)).ncard = 3 := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have hsub : f '' (Set.univ : Set TrisectorLabel) ⊆ dirC T := by
    rintro _ ⟨s, -, rfl⟩
    exact ⟨hmem s, by rw [← m3p_side_two]; exact hpar s⟩
  calc (3 : ℕ) = (f '' Set.univ).ncard := himg.symm
    _ ≤ (dirC T).ncard :=
      Set.ncard_le_ncard hsub ((m4_guideLines_finite T h).subset (fun x hx => hx.1))

/-! ## 9. The three principal statements -/

/-- **`guideLines_card`**, from the two residual hypotheses. -/
theorem card (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hC : ClassHyp T) (hD : DirHyp T) : T.guideLines.ncard = 9 :=
  le_antisymm (ncard_le_nine T h hC) (ncard_ge_nine T h hD)

/-- **`guideLines_card`** (root name, verbatim statement plus hypotheses). -/
theorem guideLines_card (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (hC : ClassHyp T) (hD : DirHyp T) : T.guideLines.ncard = 9 :=
  card T h hC hD

/-- **`point_on_two_guideLines`** (root name and statement, plus hypotheses). -/
theorem point_on_two_guideLines (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (hC : ClassHyp T) (hD : DirHyp T)
    (q : ConstellationIndex) :
    {ℓ ∈ T.guideLines | ℓ.mem (T.constellationPoint q)}.ncard = 2 :=
  m4_two_per_point_of_card_of_le T h (card T h hC hD) (index_point_le_two T h hC) q

/-- **`guideLines_direction_card`** (root name and statement, plus hypotheses). -/
theorem guideLines_direction_card (T : OrientedTriangle E o)
    (h : Injective T.constellationPoint) (hC : ClassHyp T) (hD : DirHyp T) (v : E)
    (hv : v = T.Y - T.X ∨ v = T.Z - T.Y ∨ v = T.X - T.Z) :
    {ℓ ∈ T.guideLines | Parallel v ℓ.direction}.ncard = 3 := by
  have hfin := m4_guideLines_finite T h
  have hfA : (dirA T).Finite := hfin.subset (fun x hx => hx.1)
  have hfB : (dirB T).Finite := hfin.subset (fun x hx => hx.1)
  have hfC : (dirC T).Finite := hfin.subset (fun x hx => hx.1)
  have hsum : T.guideLines.ncard = (dirA T).ncard + (dirB T).ncard + (dirC T).ncard := by
    rw [guideLines_eq_union, m4_ncard_union_of_disjoint (hfA.union hfB) hfC (disjoint_dirAB_C T),
      m4_ncard_union_of_disjoint hfA hfB (disjoint_dirAB T)]
  have h3A := three_ge_dirA T h hD
  have h3B := three_ge_dirB T h hD
  have h3C := three_ge_dirC T h hD
  have hcard := card T h hC hD
  have eA : (dirA T).ncard = 3 := by omega
  have eB : (dirB T).ncard = 3 := by omega
  have eC : (dirC T).ncard = 3 := by omega
  rcases hv with rfl | rfl | rfl
  · exact eA
  · exact eB
  · exact eC

end M8
end OrientedTriangle
end XamboMorley
