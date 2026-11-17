import XamboMorleyBase

/-!
# The nine equal-sum joins as guide-line candidates (member m4, swarm smwh1zs5u)

Direction d2 of swarm smwh1zs5u: *construct the nine guide lines*.

Everything here is additive: the root `XamboMorley.lean` is unchanged.  The file is
complete (no proof holes of any kind, no new axiom); every declaration depends only on
`propext`, `Classical.choice` and `Quot.sound` (see audit.log).

Contents
--------
§1  `m4RedPt`   -- the three red constellation points of a label-sum class.
§2  `m4L s d`   -- the nine lines: for `(s, d) : ZMod 3 x ZMod 3`, the side of the
                   `s`-th red monochrome (equilateral) triangle whose direction is the
                   `d`-th Morley side direction.  Proved: both defining red incidences
                   and `Parallel (m3pSide T d) direction`, hence `parallelToMorleySide`.
§3  `m4Six s d` -- the six constellation indices the line is expected to carry
                   (two red, two green, two blue); cardinality 6, two per colour, and
                   the elimination that a *red* index in `m4Six` is one of the two
                   defining endpoints.
§4  `m4IsGuideLine_of_certs` -- `IsGuideLine (m4L s d)` follows from the four green/blue
                   incidence certificates plus the exclusion of the other 21 indices.
§5  `m4_ncard_ge_nine`, `m4_point_two_ge`, `m4_direction_three_ge` -- the three
                   *lower bounds* needed by the principal guide-line targets, together
                   with `m4_guideLines_finite`.
§6  Canonical representatives: `m4Canon P v` is the `Line.isCanonical` member of the
                   line through `P` in direction `v`, with the same point set.  This is
                   what turns `m4L s d` into an element of `guideLines`.
§7  Distinctness of the nine lines with different Morley directions.

What is NOT proved here (and is never assumed): the four green/blue incidence
certificates `M4GBCert T h s d`, the exclusion `M4Excl T h s d`, and distinctness of
the three lines sharing one Morley direction.  Those are the exact remaining
obligations of direction d2 and are stated as named `Prop`s.
-/

namespace XamboMorley
namespace M4

open Function Set
open XamboMorley.OrientedTriangle
open XamboMorley.OrientedTriangle.OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! ## 0. Small `ZMod 3` facts -/

theorem m4_ne_shift1 (s : TrisectorLabel) : s ≠ s + 1 := by revert s; decide
theorem m4_shift1_ne (s : TrisectorLabel) : s + 1 ≠ s := by revert s; decide
theorem m4_ne_shift2 (s : TrisectorLabel) : s ≠ s + 2 := by revert s; decide
theorem m4_shift2_ne (s : TrisectorLabel) : s + 2 ≠ s := by revert s; decide
theorem m4_shift2_ne_shift1 (s : TrisectorLabel) : s + 2 ≠ s + 1 := by revert s; decide
theorem m4_shift1_ne_shift2 (s : TrisectorLabel) : s + 1 ≠ s + 2 := by revert s; decide
theorem m4_sub_self_shift1 (s : TrisectorLabel) : s - (s + 1) = 2 := by revert s; decide
theorem m4_sub_self_shift2 (s : TrisectorLabel) : s - (s + 2) = 1 := by revert s; decide

/-! ## 1. Red points of a label-sum class -/

/-- The red constellation point with label sum `s` and first label `i`. -/
noncomputable def m4RedPt (T : OrientedTriangle E o) (s i : TrisectorLabel) : E :=
  T.constellationPoint ⟨.red, i, s - i⟩

theorem m4RedPt_inj (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {s : TrisectorLabel} : Function.Injective (m4RedPt T s) := by
  intro a b hab
  have h' : (⟨.red, a, s - a⟩ : ConstellationIndex) = ⟨.red, b, s - b⟩ := h hab
  simpa using congrArg ConstellationIndex.first h'

theorem m4RedPt_ne (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {s i j : TrisectorLabel} (hij : i ≠ j) : m4RedPt T s i ≠ m4RedPt T s j := by
  intro hab
  exact hij (m4RedPt_inj T h hab)

theorem m4RedPt_self (T : OrientedTriangle E o) (s : TrisectorLabel) :
    m4RedPt T s s = T.constellationPoint ⟨.red, s, 0⟩ := by
  unfold m4RedPt
  rw [sub_self]

theorem m4RedPt_s1 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    m4RedPt T s (s + 1) = T.constellationPoint ⟨.red, s + 1, 2⟩ := by
  unfold m4RedPt
  rw [m4_sub_self_shift1]

theorem m4RedPt_s2 (T : OrientedTriangle E o) (s : TrisectorLabel) :
    m4RedPt T s (s + 2) = T.constellationPoint ⟨.red, s + 2, 1⟩ := by
  unfold m4RedPt
  rw [m4_sub_self_shift2]

/-! ## 2. The nine lines -/

/-- First label of the first endpoint. -/
def m4Lp (s d : TrisectorLabel) : TrisectorLabel :=
  if d = s then s else if d = s + 1 then s + 1 else s

/-- First label of the second endpoint. -/
def m4Lq (s d : TrisectorLabel) : TrisectorLabel :=
  if d = s then s + 2 else if d = s + 1 then s + 2 else s + 1

theorem m4Lp_ne_q : ∀ s d : TrisectorLabel, m4Lp s d ≠ m4Lq s d := by
  intro s d; revert s d; decide

theorem m4Lp_s (s : TrisectorLabel) : m4Lp s s = s := by
  unfold m4Lp; rw [if_pos rfl]

theorem m4Lp_s1 (s : TrisectorLabel) : m4Lp s (s + 1) = s + 1 := by
  unfold m4Lp; rw [if_neg (m4_shift1_ne s), if_pos rfl]

theorem m4Lp_s2 (s : TrisectorLabel) : m4Lp s (s + 2) = s := by
  unfold m4Lp; rw [if_neg (m4_shift2_ne s), if_neg (m4_shift2_ne_shift1 s)]

theorem m4Lq_s (s : TrisectorLabel) : m4Lq s s = s + 2 := by
  unfold m4Lq; rw [if_pos rfl]

theorem m4Lq_s1 (s : TrisectorLabel) : m4Lq s (s + 1) = s + 2 := by
  unfold m4Lq; rw [if_neg (m4_shift1_ne s), if_pos rfl]

theorem m4Lq_s2 (s : TrisectorLabel) : m4Lq s (s + 2) = s + 1 := by
  unfold m4Lq; rw [if_neg (m4_shift2_ne s), if_neg (m4_shift2_ne_shift1 s)]

/-- The line of the `s`-th red monochrome triangle in the `d`-th Morley direction. -/
noncomputable def m4L (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) : Line E :=
  ⟨m4RedPt T s (m4Lp s d),
    m4RedPt T s (m4Lq s d) - m4RedPt T s (m4Lp s d),
    sub_ne_zero.mpr (Ne.symm (m4RedPt_ne T h (m4Lp_ne_q s d)))⟩

theorem m4L_direction (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) :
    (m4L T h s d).direction = m4RedPt T s (m4Lq s d) - m4RedPt T s (m4Lp s d) := rfl

theorem m4L_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) : (m4L T h s d).base = m4RedPt T s (m4Lp s d) := rfl

theorem m4L_mem_p (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) : (m4L T h s d).mem (m4RedPt T s (m4Lp s d)) :=
  Line.mem_base _

theorem m4L_mem_q (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) : (m4L T h s d).mem (m4RedPt T s (m4Lq s d)) := by
  rw [Line.mem_iff_parallel, m4L_direction, m4L_base]
  exact ⟨1, by rw [one_smul]⟩

theorem m4L_dir_par_ds (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s : TrisectorLabel) : Parallel (m3pSide T s) (m4L T h s s).direction := by
  rw [m4L_direction, m4Lp_s, m4Lq_s, m4RedPt_self, m4RedPt_s2]
  have hh := Parallel.smul_right (-1) (m3p_red_par31 T s)
  rwa [show ((-1 : ℝ) • (T.constellationPoint ⟨.red, s, 0⟩ -
      T.constellationPoint ⟨.red, s + 2, 1⟩)) =
      (T.constellationPoint ⟨.red, s + 2, 1⟩ - T.constellationPoint ⟨.red, s, 0⟩) by
    rw [neg_one_smul]; abel] at hh

theorem m4L_dir_par_ds1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s : TrisectorLabel) : Parallel (m3pSide T (s + 1)) (m4L T h s (s + 1)).direction := by
  rw [m4L_direction, m4Lp_s1, m4Lq_s1, m4RedPt_s1, m4RedPt_s2]
  exact m3p_red_par23 T s

theorem m4L_dir_par_ds2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s : TrisectorLabel) : Parallel (m3pSide T (s + 2)) (m4L T h s (s + 2)).direction := by
  rw [m4L_direction, m4Lp_s2, m4Lq_s2, m4RedPt_self, m4RedPt_s1]
  exact m3p_red_par12 T s

/-- `m4L` has the `d`-th Morley side direction, for every `(s, d)`. -/
theorem m4L_dir_par (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) : Parallel (m3pSide T d) (m4L T h s d).direction := by
  have hd : d = s ∨ d = s + 1 ∨ d = s + 2 := by
    have h0 : (d - s) = 0 ∨ (d - s) = 1 ∨ (d - s) = 2 := zmod3_cases (d - s)
    have e1 : d - s = 0 → d = s := fun h' => by
      rw [sub_eq_iff_eq_add] at h'; simpa using h'
    have e2 : d - s = 1 → d = s + 1 := fun h' => by
      rw [sub_eq_iff_eq_add] at h'; rw [h']; abel
    have e3 : d - s = 2 → d = s + 2 := fun h' => by
      rw [sub_eq_iff_eq_add] at h'; rw [h']; abel
    rcases h0 with h0 | h0 | h0
    · exact Or.inl (e1 h0)
    · exact Or.inr (Or.inl (e2 h0))
    · exact Or.inr (Or.inr (e3 h0))
  rcases hd with hd | hd | hd
  · rw [hd]; exact m4L_dir_par_ds T h s
  · rw [hd]; exact m4L_dir_par_ds1 T h s
  · rw [hd]; exact m4L_dir_par_ds2 T h s

/-- The first conjunct of `IsGuideLine` for the nine constructed lines. -/
theorem m4L_ptM (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) : T.parallelToMorleySide (m4L T h s d).direction :=
  m3p_side_ptM T d (m4L_dir_par T h s d)

/-! ## 3. The six-point set of a line -/

/-- The six constellation indices that `m4L s d` is expected to carry:
two red, two green, two blue. -/
def m4Six (s d : TrisectorLabel) : Finset ConstellationIndex :=
  {⟨.red, m4Lp s d, s - m4Lp s d⟩, ⟨.red, m4Lq s d, s - m4Lq s d⟩,
   ⟨.green, s - m4Lp s d, d + m4Lp s d⟩, ⟨.green, s - m4Lq s d, d + m4Lq s d⟩,
   ⟨.blue, s - d - 1 - m4Lp s d, m4Lp s d⟩, ⟨.blue, s - d - 1 - m4Lq s d, m4Lq s d⟩}

theorem m4Six_card (s d : TrisectorLabel) : (m4Six s d).card = 6 := by
  revert s d; decide

theorem m4Six_two_per_color (s d : TrisectorLabel) (c : TrisectorColor) :
    ((m4Six s d).filter (fun q => q.color = c)).card = 2 := by
  revert s d; cases c <;> decide

theorem m4Six_mem_red_left (s d : TrisectorLabel) :
    (⟨.red, m4Lp s d, s - m4Lp s d⟩ : ConstellationIndex) ∈ m4Six s d := by
  unfold m4Six; simp

theorem m4Six_mem_red_right (s d : TrisectorLabel) :
    (⟨.red, m4Lq s d, s - m4Lq s d⟩ : ConstellationIndex) ∈ m4Six s d := by
  unfold m4Six; simp

/-- A red index in `m4Six s d` is one of the two defining endpoints. -/
theorem m4Six_red_elim (s d f g : TrisectorLabel)
    (hmem : (⟨.red, f, g⟩ : ConstellationIndex) ∈ m4Six s d) :
    (⟨.red, f, g⟩ : ConstellationIndex) = ⟨.red, m4Lp s d, s - m4Lp s d⟩ ∨
      (⟨.red, f, g⟩ : ConstellationIndex) = ⟨.red, m4Lq s d, s - m4Lq s d⟩ := by
  unfold m4Six at hmem
  rcases Finset.mem_insert.mp hmem with h | h
  · exact Or.inl h
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inr h
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by simp)
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by simp)
  rcases Finset.mem_insert.mp h with h | h
  · exact absurd (congrArg ConstellationIndex.color h) (by simp)
  rw [Finset.mem_singleton] at h
  exact absurd (congrArg ConstellationIndex.color h) (by simp)

/-! ## 4. `IsGuideLine` from the incidence certificates -/

/-- The green/blue incidence certificates for `(s, d)`: the four non-red members of
`m4Six s d` are incident with `m4L s d`. -/
def M4GBCert (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) : Prop :=
  ∀ q ∈ m4Six s d, q.color ≠ TrisectorColor.red → (m4L T h s d).mem (T.constellationPoint q)

/-- No constellation point outside `m4Six s d` is incident with `m4L s d`. -/
def M4Excl (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) : Prop :=
  ∀ q : ConstellationIndex, (m4L T h s d).mem (T.constellationPoint q) → q ∈ m4Six s d

/-- **All six incidences plus the exclusion give `IsGuideLine`.** -/
theorem m4IsGuideLine_of_certs (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    (s d : TrisectorLabel) (hgb : M4GBCert T h s d) (hex : M4Excl T h s d) :
    T.IsGuideLine (m4L T h s d) := by
  have hinc : ∀ q ∈ m4Six s d, (m4L T h s d).mem (T.constellationPoint q) := by
    intro q hq
    rcases q with ⟨c, f, g⟩
    by_cases hc : c = TrisectorColor.red
    · subst hc
      rcases m4Six_red_elim s d f g hq with h' | h'
      · rw [h']; exact m4L_mem_p T h s d
      · rw [h']; exact m4L_mem_q T h s d
    · exact hgb _ hq hc
  refine ⟨m4L_ptM T h s d, ?_, ?_⟩
  · have hset : {q : ConstellationIndex | (m4L T h s d).mem (T.constellationPoint q)}
        = ↑(m4Six s d) := by
      ext q
      simp only [Finset.mem_coe, Set.mem_ofPred_eq]
      exact ⟨hex q, hinc q⟩
    rw [hset, Set.ncard_coe_finset, m4Six_card]
  · intro c
    have hset : {q : ConstellationIndex | q.color = c ∧
          (m4L T h s d).mem (T.constellationPoint q)}
        = ↑((m4Six s d).filter (fun q => q.color = c)) := by
      ext q
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq]
      exact ⟨fun hp => ⟨hex q hp.2, hp.1⟩, fun hp => ⟨hp.2, hinc q hp.1⟩⟩
    rw [hset, Set.ncard_coe_finset, m4Six_two_per_color]


open Function Set
open scoped RealInnerProductSpace InnerProductSpace
open XamboMorley.OrientedTriangle
open XamboMorley.OrientedTriangle.OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-- The unit vector in the direction of `v`. -/
noncomputable def m4Unit (v : E) : E := (‖v‖)⁻¹ • v

theorem m4Unit_norm {v : E} (hv : v ≠ 0) : ‖m4Unit v‖ = 1 := by
  rw [m4Unit, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem m4Unit_ne {v : E} (hv : v ≠ 0) : m4Unit v ≠ 0 := by
  intro h
  have h1 := m4Unit_norm hv
  rw [h, norm_zero] at h1
  norm_num at h1

theorem m4e1_ne (o : Orientation ℝ E (Fin 2)) : e₁ o ≠ 0 := by
  intro h0
  have h : ‖e₁ o‖ = 1 := (positiveBasis o).orthonormal.1 0
  rw [h0, norm_zero] at h
  norm_num at h

/-- The direction of the canonical representative: the unit direction, or its negative
according to the angular sector of `Line.isCanonical`. -/
noncomputable def m4Dir (o : Orientation ℝ E (Fin 2)) (v : E) : E :=
  if (o.oangle (e₁ o) (m4Unit v)).toReal ∈ Set.Ico 0 Real.pi then m4Unit v else -(m4Unit v)

variable (o)

theorem m4Dir_eq_or (v : E) :
    m4Dir o v = m4Unit v ∨ m4Dir o v = -(m4Unit v) := by
  unfold m4Dir
  by_cases hc : (o.oangle (e₁ o) (m4Unit v)).toReal ∈ Set.Ico 0 Real.pi
  · exact Or.inl (if_pos hc)
  · exact Or.inr (if_neg hc)

theorem m4Dir_norm {v : E} (hv : v ≠ 0) : ‖m4Dir o v‖ = 1 := by
  rcases m4Dir_eq_or o v with h | h <;> rw [h]
  · exact m4Unit_norm hv
  · rw [norm_neg]; exact m4Unit_norm hv

theorem m4Dir_ne {v : E} (hv : v ≠ 0) : m4Dir o v ≠ 0 := by
  intro h
  have h1 := m4Dir_norm (o := o) hv
  rw [h, norm_zero] at h1
  norm_num at h1

theorem m4Dir_par {v : E} (hv : v ≠ 0) : Parallel v (m4Dir o v) := by
  rcases m4Dir_eq_or o v with h | h
  · rw [h, m4Unit]
    exact ⟨(‖v‖)⁻¹, rfl⟩
  · rw [h, m4Unit]
    exact ⟨-(‖v‖)⁻¹, by rw [neg_smul]⟩

theorem m4Dir_sector {v : E} (hv : v ≠ 0) :
    (o.oangle (e₁ o) (m4Dir o v)).toReal ∈ Set.Ico 0 Real.pi := by
  have hu : m4Unit v ≠ 0 := m4Unit_ne hv
  have hlow : -Real.pi < (o.oangle (e₁ o) (m4Unit v)).toReal := Real.Angle.neg_pi_lt_toReal _
  have hupp : (o.oangle (e₁ o) (m4Unit v)).toReal ≤ Real.pi := Real.Angle.toReal_le_pi _
  unfold m4Dir
  by_cases hc : (o.oangle (e₁ o) (m4Unit v)).toReal ∈ Set.Ico 0 Real.pi
  · rw [if_pos hc]; exact hc
  · rw [if_neg hc]
    have hneg : o.oangle (e₁ o) (-(m4Unit v))
        = o.oangle (e₁ o) (m4Unit v) + (Real.pi : Real.Angle) :=
      Orientation.oangle_neg_right (o := o) (x := e₁ o) (y := m4Unit v) (m4e1_ne o) hu
    have hcoe : o.oangle (e₁ o) (m4Unit v) + (Real.pi : Real.Angle)
        = (((o.oangle (e₁ o) (m4Unit v)).toReal + Real.pi : ℝ) : Real.Angle) := by
      conv_lhs => rw [← Real.Angle.coe_toReal (o.oangle (e₁ o) (m4Unit v))]
      rw [← Real.Angle.coe_add]
    rw [hneg, hcoe]
    have hcases : (o.oangle (e₁ o) (m4Unit v)).toReal < 0 ∨
        (o.oangle (e₁ o) (m4Unit v)).toReal = Real.pi := by
      rcases lt_trichotomy ((o.oangle (e₁ o) (m4Unit v)).toReal) 0 with h | h | h
      · exact Or.inl h
      · exfalso
        exact hc ⟨le_of_eq h.symm, by rw [h]; exact Real.pi_pos⟩
      · refine Or.inr ?_
        have hlt : ¬ (o.oangle (e₁ o) (m4Unit v)).toReal < Real.pi :=
          fun hlt => hc ⟨le_of_lt h, hlt⟩
        linarith
    rcases hcases with hlt | heq
    · have hval : (((o.oangle (e₁ o) (m4Unit v)).toReal + Real.pi : ℝ) : Real.Angle).toReal
          = (o.oangle (e₁ o) (m4Unit v)).toReal + Real.pi := by
        rw [Real.Angle.toReal_coe_eq_self_iff]
        exact ⟨by linarith, by linarith⟩
      rw [hval]
      exact ⟨by linarith, by linarith⟩
    · rw [heq, show Real.pi + Real.pi = 2 * Real.pi by ring, Real.Angle.coe_two_pi]
      simp [Real.pi_pos]

/-- The foot of the perpendicular from the origin to the line through `P` in
direction `u`. -/
noncomputable def m4Foot (P u : E) : E := P - (⟪P, u⟫_ℝ) • u

theorem m4Foot_inner {P u : E} (hu : ‖u‖ = 1) : ⟪m4Foot P u, u⟫_ℝ = 0 := by
  rw [m4Foot, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
  ring

theorem m4Foot_mem {P v : E} (hv : v ≠ 0) :
    (⟨P, v, hv⟩ : Line E).mem (m4Foot P (m4Dir o v)) := by
  obtain ⟨r, hr⟩ := m4Dir_par (o := o) hv
  rw [Line.mem_iff_parallel]
  refine ⟨-(⟪P, m4Dir o v⟫_ℝ * r), ?_⟩
  rw [m4Foot, hr]
  rw [show P - ⟪P, r • v⟫_ℝ • (r • v) - P = -((⟪P, r • v⟫_ℝ * r) • v) by
    rw [smul_smul]; abel]
  rw [neg_smul]

/-- The canonical representative of the line through `P` in direction `v`. -/
noncomputable def m4Canon (P v : E) (hv : v ≠ 0) : Line E :=
  ⟨m4Foot P (m4Dir o v), m4Dir o v, m4Dir_ne o hv⟩

theorem m4Canon_isCanonical {P v : E} (hv : v ≠ 0) :
    Line.isCanonical o (m4Canon (o := o) P v hv) :=
  ⟨m4Dir_norm o hv, m4Foot_inner (m4Dir_norm o hv), m4Dir_sector o hv⟩

theorem m4Canon_mem_P {P v : E} (hv : v ≠ 0) : (m4Canon (o := o) P v hv).mem P := by
  refine ⟨⟪P, m4Dir o v⟫_ℝ, ?_⟩
  show P = m4Foot P (m4Dir o v) + ⟪P, m4Dir o v⟫_ℝ • m4Dir o v
  rw [m4Foot]
  exact (sub_add_cancel P (⟪P, m4Dir o v⟫_ℝ • m4Dir o v)).symm

/-- Membership from parallelism to a point of the line (local copy). -/
theorem m4_mem_iff_parallel_of_memC {ℓ : Line E} {P X : E} (hP : ℓ.mem P) :
    ℓ.mem X ↔ Parallel ℓ.direction (X - P) := by
  constructor
  · intro hX
    exact ℓ.parallel_of_mem_sub hP hX
  · intro h
    obtain ⟨t, ht⟩ := h
    obtain ⟨s, hs⟩ := hP
    exact ⟨s + t, by
      rw [show X = P + t • ℓ.direction from by rw [← ht]; abel, hs, add_smul]; abel⟩

/-- Adding a multiple of the direction does not change the parallel class. -/
theorem m4_par_add_smul {v W : E} (c : ℝ) : Parallel v (W + c • v) ↔ Parallel v W := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t - c, ?_⟩
    rw [sub_smul]
    rw [← ht]
    abel
  · rintro ⟨t, ht⟩
    exact ⟨t + c, by rw [add_smul, ← ht]⟩

/-- **The canonical representative has the same point set as `⟨P, v⟩`.** -/
theorem m4Canon_mem_iff {P v : E} (hv : v ≠ 0) (X : E) :
    (m4Canon (o := o) P v hv).mem X ↔ (⟨P, v, hv⟩ : Line E).mem X := by
  obtain ⟨r, hr⟩ := m4Dir_par (o := o) hv
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hr
    exact m4Dir_ne o hv hr
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(s - ⟪P, m4Dir o v⟫_ℝ) * r, ?_⟩
    rw [hs]
    show m4Foot P (m4Dir o v) + s • m4Dir o v
      = P + ((s - ⟪P, m4Dir o v⟫_ℝ) * r) • v
    rw [m4Foot, hr]
    module
  · rintro ⟨t, ht⟩
    refine ⟨⟪P, m4Dir o v⟫_ℝ + t * r⁻¹, ?_⟩
    rw [ht]
    show P + t • v = m4Foot P (m4Dir o v) + (⟪P, m4Dir o v⟫_ℝ + t * r⁻¹) • m4Dir o v
    rw [m4Foot, hr, add_smul, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hr0, mul_one]
    abel


open Function Set
open XamboMorley.OrientedTriangle
open XamboMorley.OrientedTriangle.OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! ## 5. `guideLines` is finite, and the lower-bound packaging -/

theorem m4Side_ne (T : OrientedTriangle E o) (d : TrisectorLabel) : m3pSide T d ≠ 0 := by
  rcases zmod3_cases d with h | h | h
  · rw [h, m3p_side_zero]; exact T.m2_Y_sub_X_ne
  · rw [h, m3p_side_one]; exact T.m2_Z_sub_Y_ne
  · rw [h, m3p_side_two]
    intro hzero
    have hdist : dist T.Z T.X = 0 := by
      rw [dist_eq_norm, show T.Z - T.X = -(T.X - T.Z) from by abel, hzero, neg_zero, norm_zero]
    have hpos : 0 < dist T.Z T.X := by
      rw [T.morley_side_lengths.2.2]
      have h1 := m7_delta_pos T; have h2 := m7_sin_alpha_pos T
      have h3 := m7_sin_beta_pos T; have h4 := m7_sin_gamma_pos T
      positivity
    linarith

/-- A point on every guide line: used for finiteness. -/
theorem m4_guide_nonempty (T : OrientedTriangle E o) {ℓ : Line E} (hℓ : T.IsGuideLine ℓ) :
    ∃ q : ConstellationIndex, ℓ.mem (T.constellationPoint q) := by
  have h6 := hℓ.2.1
  have hpos : 0 < {q : ConstellationIndex | ℓ.mem (T.constellationPoint q)}.ncard := by
    rw [h6]; norm_num
  obtain ⟨q, hq⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  exact ⟨q, hq⟩

/-- The Morley direction index of a guide line. -/
theorem m4_guide_dir (T : OrientedTriangle E o) {ℓ : Line E} (hℓ : T.IsGuideLine ℓ) :
    ∃ d : TrisectorLabel, Parallel (m3pSide T d) ℓ.direction := by
  rcases hℓ.1 with h | h | h
  · exact ⟨0, by rw [m3p_side_zero]; exact h⟩
  · exact ⟨1, by rw [m3p_side_one]; exact h⟩
  · exact ⟨2, by rw [m3p_side_two]; exact h⟩

/-- Membership from parallelism to a point of the line. -/
theorem m4_mem_iff_parallel_of_mem {ℓ : Line E} {P X : E} (hP : ℓ.mem P) :
    ℓ.mem X ↔ Parallel ℓ.direction (X - P) := by
  constructor
  · intro hX
    exact ℓ.parallel_of_mem_sub hP hX
  · intro h
    obtain ⟨t, ht⟩ := h
    obtain ⟨s, hs⟩ := hP
    exact ⟨s + t, by
      rw [show X = P + t • ℓ.direction from by rw [← ht]; abel, hs, add_smul]; abel⟩

/-- **Two canonical lines with a common point and parallel directions coincide.** -/
theorem m4_eq_of_mem_common (T : OrientedTriangle E o) {ℓ ℓ' : Line E}
    (hc : Line.isCanonical o ℓ) (hc' : Line.isCanonical o ℓ') {P : E}
    (hP : ℓ.mem P) (hP' : ℓ'.mem P) (hpar : Parallel ℓ.direction ℓ'.direction) : ℓ = ℓ' := by
  refine isCanonical_eq_of_mem_iff hc hc' (fun X => ?_)
  rw [m4_mem_iff_parallel_of_mem hP, m4_mem_iff_parallel_of_mem hP']
  constructor
  · intro hX
    exact (parallel_comm ℓ.direction_ne_zero ℓ'.direction_ne_zero hpar).trans hX
  · intro hX
    exact hpar.trans hX

/-- **`guideLines` is finite.**  Each guide line is determined by one of its six
constellation points together with one of the three Morley directions. -/
theorem m4_guideLines_finite (T : OrientedTriangle E o) : T.guideLines.Finite := by
  rw [← Set.finite_coe_iff]
  have hmem : ∀ x : {ℓ // ℓ ∈ T.guideLines},
      ∃ q : ConstellationIndex, x.val.mem (T.constellationPoint q) :=
    fun x => m4_guide_nonempty T x.property.1
  have hdir : ∀ x : {ℓ // ℓ ∈ T.guideLines},
      ∃ d : TrisectorLabel, Parallel (m3pSide T d) x.val.direction :=
    fun x => m4_guide_dir T x.property.1
  let f : {ℓ // ℓ ∈ T.guideLines} → ConstellationIndex × TrisectorLabel :=
    fun x => (Classical.choose (hmem x), Classical.choose (hdir x))
  have hf : Function.Injective f := by
    intro x y hxy
    have hq : Classical.choose (hmem x) = Classical.choose (hmem y) := congrArg Prod.fst hxy
    have hd : Classical.choose (hdir x) = Classical.choose (hdir y) := congrArg Prod.snd hxy
    have hPx : x.val.mem (T.constellationPoint (Classical.choose (hmem x))) :=
      Classical.choose_spec (hmem x)
    have hPy : y.val.mem (T.constellationPoint (Classical.choose (hmem x))) := by
      rw [hq]; exact Classical.choose_spec (hmem y)
    have hdx : Parallel (m3pSide T (Classical.choose (hdir x))) x.val.direction :=
      Classical.choose_spec (hdir x)
    have hdy : Parallel (m3pSide T (Classical.choose (hdir y))) y.val.direction :=
      Classical.choose_spec (hdir y)
    have hdeq : m3pSide T (Classical.choose (hdir x))
        = m3pSide T (Classical.choose (hdir y)) := by rw [hd]
    have hdyn : Parallel y.val.direction (m3pSide T (Classical.choose (hdir x))) := by
      rw [hdeq]; exact parallel_comm (m4Side_ne T _) y.val.direction_ne_zero hdy
    have hpar : Parallel y.val.direction x.val.direction := hdyn.trans hdx
    exact Subtype.ext (m4_eq_of_mem_common T y.property.2 x.property.2 hPy hPx hpar).symm
  exact Finite.of_injective f hf

/-- **Lower bound for `guideLines_card`**: nine pairwise distinct guide lines give
`9 ≤ T.guideLines.ncard`. -/
theorem m4_ncard_ge_nine (T : OrientedTriangle E o) (ℓ : TrisectorLabel → TrisectorLabel → Line E)
    (hmem : ∀ s d, ℓ s d ∈ T.guideLines)
    (hinj : ∀ s d s' d', ℓ s d = ℓ s' d' → s = s' ∧ d = d') :
    9 ≤ T.guideLines.ncard := by
  have hinjOn : Function.Injective (fun p : TrisectorLabel × TrisectorLabel => ℓ p.1 p.2) := by
    intro p q hpq
    obtain ⟨h1, h2⟩ := hinj p.1 p.2 q.1 q.2 hpq
    exact Prod.ext h1 h2
  have hsub : ((fun p : TrisectorLabel × TrisectorLabel => ℓ p.1 p.2) '' Set.univ)
      ⊆ T.guideLines := by
    rintro x ⟨p, -, rfl⟩
    exact hmem p.1 p.2
  have himg : ((fun p : TrisectorLabel × TrisectorLabel => ℓ p.1 p.2) '' Set.univ).ncard = 9 := by
    rw [Set.ncard_image_of_injective _ hinjOn, Set.ncard_univ, Nat.card_eq_fintype_card]
    simp [Fintype.card_prod, ZMod.card]
  calc (9 : ℕ) = ((fun p : TrisectorLabel × TrisectorLabel => ℓ p.1 p.2) '' Set.univ).ncard :=
        himg.symm
    _ ≤ T.guideLines.ncard := Set.ncard_le_ncard hsub (m4_guideLines_finite T)

/-- **Lower bound for `point_on_two_guideLines`**: two distinct guide lines through a
constellation point give `2 ≤` the count. -/
theorem m4_point_two_ge (T : OrientedTriangle E o) (q : ConstellationIndex)
    {ℓ ℓ' : Line E} (hℓ : ℓ ∈ T.guideLines) (hℓ' : ℓ' ∈ T.guideLines) (hne : ℓ ≠ ℓ')
    (hm : ℓ.mem (T.constellationPoint q)) (hm' : ℓ'.mem (T.constellationPoint q)) :
    2 ≤ {ℓ : Line E | ℓ ∈ T.guideLines ∧ ℓ.mem (T.constellationPoint q)}.ncard := by
  have hfin : {ℓ : Line E | ℓ ∈ T.guideLines ∧ ℓ.mem (T.constellationPoint q)}.Finite :=
    (m4_guideLines_finite T).subset (fun x hx => hx.1)
  have hsub : ({ℓ, ℓ'} : Set (Line E)) ⊆
      {ℓ : Line E | ℓ ∈ T.guideLines ∧ ℓ.mem (T.constellationPoint q)} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨hℓ, hm⟩
    · exact ⟨hℓ', hm'⟩
  have h2 : ({ℓ, ℓ'} : Set (Line E)).ncard = 2 := Set.ncard_pair hne
  calc (2 : ℕ) = ({ℓ, ℓ'} : Set (Line E)).ncard := h2.symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

/-- **Lower bound for `guideLines_direction_card`**: three distinct guide lines
parallel to one Morley side direction give `3 ≤` the count. -/
theorem m4_direction_three_ge (T : OrientedTriangle E o) (v : E)
    {ℓ₀ ℓ₁ ℓ₂ : Line E} (h₀ : ℓ₀ ∈ T.guideLines) (h₁ : ℓ₁ ∈ T.guideLines)
    (h₂ : ℓ₂ ∈ T.guideLines)
    (hne₀₁ : ℓ₀ ≠ ℓ₁) (hne₀₂ : ℓ₀ ≠ ℓ₂) (hne₁₂ : ℓ₁ ≠ ℓ₂)
    (hp₀ : Parallel v ℓ₀.direction) (hp₁ : Parallel v ℓ₁.direction)
    (hp₂ : Parallel v ℓ₂.direction) :
    3 ≤ {ℓ : Line E | ℓ ∈ T.guideLines ∧ Parallel v ℓ.direction}.ncard := by
  have hfin : {ℓ : Line E | ℓ ∈ T.guideLines ∧ Parallel v ℓ.direction}.Finite :=
    (m4_guideLines_finite T).subset (fun x hx => hx.1)
  have hsub : ({ℓ₀, ℓ₁, ℓ₂} : Set (Line E)) ⊆
      {ℓ : Line E | ℓ ∈ T.guideLines ∧ Parallel v ℓ.direction} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨h₀, hp₀⟩
    · exact ⟨h₁, hp₁⟩
    · exact ⟨h₂, hp₂⟩
  have h3 : ({ℓ₀, ℓ₁, ℓ₂} : Set (Line E)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hne₀₁, hne₀₂]), Set.ncard_pair hne₁₂]
  calc (3 : ℕ) = ({ℓ₀, ℓ₁, ℓ₂} : Set (Line E)).ncard := h3.symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

/-! ## 6. Distinctness of the nine lines for different Morley directions -/

/-- The three Morley side directions are pairwise non-parallel. -/
theorem m4_side_not_parallel (T : OrientedTriangle E o) {d d' : TrisectorLabel} (h : d ≠ d') :
    ¬ Parallel (m3pSide T d) (m3pSide T d') := by
  rcases zmod3_cases d with hd | hd | hd <;> rcases zmod3_cases d' with hd' | hd' | hd'
  · exact absurd (hd.trans hd'.symm) h
  · rw [hd, hd', m3p_side_zero, m3p_side_one]; exact T.m4_not_parallel_morley.1
  · rw [hd, hd', m3p_side_zero, m3p_side_two]
    exact fun hc =>
      T.m4_not_parallel_morley.2.2 (parallel_comm (m4Side_ne T 0) (m4Side_ne T 2) hc)
  · rw [hd, hd', m3p_side_one, m3p_side_zero]
    exact fun hc =>
      T.m4_not_parallel_morley.1 (parallel_comm (m4Side_ne T 1) (m4Side_ne T 0) hc)
  · exact absurd (hd.trans hd'.symm) h
  · rw [hd, hd', m3p_side_one, m3p_side_two]; exact T.m4_not_parallel_morley.2.1
  · rw [hd, hd', m3p_side_two, m3p_side_zero]; exact T.m4_not_parallel_morley.2.2
  · rw [hd, hd', m3p_side_two, m3p_side_one]
    exact fun hc =>
      T.m4_not_parallel_morley.2.1 (parallel_comm (m4Side_ne T 2) (m4Side_ne T 1) hc)
  · exact absurd (hd.trans hd'.symm) h

/-- **The nine lines are distinct whenever their Morley directions differ.** -/
theorem m4L_ne_of_ne_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {s d s' d' : TrisectorLabel} (hdd : d ≠ d') : m4L T h s d ≠ m4L T h s' d' := by
  intro heq
  have hpar : Parallel (m3pSide T d) (m3pSide T d') := by
    have h1 : (m4L T h s' d').direction = (m4L T h s d).direction := by rw [heq]
    have h2 : Parallel (m4L T h s d).direction (m3pSide T d') := by
      rw [← h1]
      exact parallel_comm (m4Side_ne T d') (m4L T h s' d').direction_ne_zero
        (m4L_dir_par T h s' d')
    exact (m4L_dir_par T h s d).trans h2
  exact m4_side_not_parallel T hdd hpar


end M4
end XamboMorley
