/-
  Member m3 (swarm smwh7aexl), direction d5: NINE_EXACT_GUIDE_MEMBERS.

  Part A (unconditional): the canonical representative of a geometric line and the
  canonical line through two distinct points.  `guideLines` is the set of lines which
  are `IsGuideLine` *and* `Line.isCanonical`; the root only contains the uniqueness
  statement `isCanonical_eq_of_mem_iff`, no construction.  Everything below supplies
  the missing construction, so that concrete guide lines can be exhibited as elements
  of `T.guideLines` without touching the root.
-/
import XamboMorleyBase

noncomputable section
open scoped Real RealInnerProductSpace ComplexConjugate Matrix
open Function Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace XamboMorley
namespace OrientedTriangle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)] {o : Orientation ℝ E (Fin 2)}

/-! ### A toolbox for `Parallel` -/

theorem m3_par_sub_smul {u v : E} {r : ℝ} (h : Parallel u v) : Parallel u (v - r • u) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a - r, (sub_smul a r u).symm⟩

theorem m3_par_trans {u v w : E} (h1 : Parallel u v) (h2 : Parallel v w) : Parallel u w := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨b * a, smul_smul b a u⟩

theorem m3_par_neg_right_iff {u v : E} : Parallel u (-v) ↔ Parallel u v := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨-r, by rw [neg_smul, ← hr, neg_neg]⟩
  · rintro ⟨r, hr⟩
    exact ⟨-r, by rw [neg_smul, ← hr]⟩

theorem m3_par_add_smul {u v : E} (h : Parallel u v) {r : ℝ} : Parallel u (v + r • u) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a + r, (add_smul a r u).symm⟩

/-- Replacing a nonzero vector by a parallel one does not change the parallelism class. -/
theorem m3_par_par_iff {u v w : E} (hu : u ≠ 0) (hv : v ≠ 0) (h : Parallel u v) :
    Parallel u w ↔ Parallel v w := by
  obtain ⟨a, rfl⟩ := h
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hv
    exact hv rfl
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b * a⁻¹, by rw [hb, smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]⟩
  · rintro ⟨b, hb⟩
    exact ⟨b * a, by rw [hb, smul_smul]⟩

/-! ### Unit vector in a given direction -/

/-- The unit vector in the direction of `v`. -/
def m3unit (v : E) : E := (‖v‖)⁻¹ • v

theorem m3unit_ne_zero {v : E} (hv : v ≠ 0) : m3unit v ≠ 0 := by
  unfold m3unit
  exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hv)) hv

theorem m3unit_norm {v : E} (hv : v ≠ 0) : ‖m3unit v‖ = 1 := by
  unfold m3unit
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem m3unit_parallel {v : E} (hv : v ≠ 0) : Parallel v (m3unit v) :=
  ⟨‖v‖⁻¹, rfl⟩

theorem m3unit_norm_smul {v : E} (hv : v ≠ 0) : ‖v‖ • m3unit v = v := by
  unfold m3unit
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

/-! ### Picking the representative in the angular sector `[0, π)` -/

/-- The direction sign which puts the angle with `e₁ o` in the sector `[0, π)`. -/
def m3sgnDir (o : Orientation ℝ E (Fin 2)) (v : E) : E :=
  if 0 ≤ (o.oangle (e₁ o) (m3unit v)).toReal ∧
      (o.oangle (e₁ o) (m3unit v)).toReal < Real.pi then m3unit v else -(m3unit v)

theorem m3sgnDir_eq_or_neg (v : E) :
    m3sgnDir o v = m3unit v ∨ m3sgnDir o v = -(m3unit v) := by
  rw [m3sgnDir]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem m3sgnDir_parallel {v : E} (hv : v ≠ 0) : Parallel v (m3sgnDir o v) := by
  rcases m3sgnDir_eq_or_neg (o := o) v with h | h
  · rw [h]; exact m3unit_parallel hv
  · rw [h]
    obtain ⟨r, hr⟩ := m3unit_parallel hv
    exact ⟨-r, by rw [hr, neg_smul]⟩

theorem m3sgnDir_norm {v : E} (hv : v ≠ 0) : ‖m3sgnDir o v‖ = 1 := by
  rcases m3sgnDir_eq_or_neg (o := o) v with h | h
  · rw [h]; exact m3unit_norm hv
  · rw [h, norm_neg]; exact m3unit_norm hv

theorem m3sgnDir_ne_zero {v : E} (hv : v ≠ 0) : m3sgnDir o v ≠ 0 := by
  rcases m3sgnDir_eq_or_neg (o := o) v with h | h
  · rw [h]; exact m3unit_ne_zero hv
  · rw [h]; exact neg_ne_zero.mpr (m3unit_ne_zero hv)

theorem m3sgnDir_sector {v : E} (hv : v ≠ 0) :
    (o.oangle (e₁ o) (m3sgnDir o v)).toReal ∈ Set.Ico 0 Real.pi := by
  have he1 : e₁ o ≠ 0 := by
    have h : ‖e₁ o‖ = 1 := (positiveBasis o).orthonormal.1 0
    exact norm_ne_zero_iff.mp (by rw [h]; norm_num)
  by_cases hA : 0 ≤ (o.oangle (e₁ o) (m3unit v)).toReal ∧
      (o.oangle (e₁ o) (m3unit v)).toReal < Real.pi
  · rw [m3sgnDir, if_pos hA]
    exact hA
  · rw [m3sgnDir, if_neg hA,
      Orientation.oangle_neg_right (o := o) he1 (m3unit_ne_zero hv)]
    rcases lt_or_ge (o.oangle (e₁ o) (m3unit v)).toReal 0 with hneg | hpos
    · have hcoe : (((o.oangle (e₁ o) (m3unit v)).toReal + Real.pi : ℝ) : Real.Angle)
          = o.oangle (e₁ o) (m3unit v) + (Real.pi : Real.Angle) := by
        rw [Real.Angle.coe_add, Real.Angle.coe_toReal]
      have hval : (((o.oangle (e₁ o) (m3unit v)).toReal + Real.pi : ℝ) : Real.Angle).toReal
          = (o.oangle (e₁ o) (m3unit v)).toReal + Real.pi := by
        rw [Real.Angle.toReal_coe_eq_self_iff]
        have h1 := Real.Angle.neg_pi_lt_toReal (o.oangle (e₁ o) (m3unit v))
        constructor <;> linarith
      rw [← hcoe, hval]
      have h1 := Real.Angle.neg_pi_lt_toReal (o.oangle (e₁ o) (m3unit v))
      constructor <;> linarith
    · have hle := Real.Angle.toReal_le_pi (o.oangle (e₁ o) (m3unit v))
      have heq : (o.oangle (e₁ o) (m3unit v)).toReal = Real.pi :=
        le_antisymm hle (le_of_not_gt fun h => hA ⟨hpos, h⟩)
      have hzero : o.oangle (e₁ o) (m3unit v) + (Real.pi : Real.Angle) = 0 := by
        conv_lhs => rw [← Real.Angle.coe_toReal (o.oangle (e₁ o) (m3unit v))]
        rw [← Real.Angle.coe_add,
          show (o.oangle (e₁ o) (m3unit v)).toReal + Real.pi = 2 * Real.pi by
            rw [heq]; ring]
        exact Real.Angle.coe_two_pi
      rw [hzero, Real.Angle.toReal_zero]
      exact ⟨le_refl 0, Real.pi_pos⟩

/-! ### The canonical line through two distinct points -/

/-- The canonical representative of the line through `P` and `Q` (`P ≠ Q`):
unit direction with angle in `[0, π)`, base the perpendicular foot of the origin. -/
def m3lineThrough (P Q : E) (h : P ≠ Q) : Line E :=
  ⟨P - ⟪P, m3sgnDir o (Q - P)⟫ • m3sgnDir o (Q - P),
    m3sgnDir o (Q - P), m3sgnDir_ne_zero (o := o) (sub_ne_zero.mpr h.symm)⟩

theorem m3lineThrough_mem_iff (P Q : E) (h : P ≠ Q) (X : E) :
    (m3lineThrough (o := o) P Q h).mem X ↔ Parallel (Q - P) (X - P) := by
  have hPQ : Q - P ≠ 0 := sub_ne_zero.mpr h.symm
  have hu : m3sgnDir o (Q - P) ≠ 0 := m3sgnDir_ne_zero (o := o) hPQ
  rw [m3lineThrough, Line.mem_iff_parallel]
  have hbase : X - (P - ⟪P, m3sgnDir o (Q - P)⟫ • m3sgnDir o (Q - P))
      = (X - P) + ⟪P, m3sgnDir o (Q - P)⟫ • m3sgnDir o (Q - P) := by abel
  rw [hbase]
  have hsub : ((X - P) + ⟪P, m3sgnDir o (Q - P)⟫ • m3sgnDir o (Q - P))
      - ⟪P, m3sgnDir o (Q - P)⟫ • m3sgnDir o (Q - P) = X - P := by abel
  have hkey : Parallel (m3sgnDir o (Q - P))
      ((X - P) + ⟪P, m3sgnDir o (Q - P)⟫ • m3sgnDir o (Q - P))
      ↔ Parallel (m3sgnDir o (Q - P)) (X - P) := by
    constructor
    · intro hh
      have h2 := m3_par_sub_smul (u := m3sgnDir o (Q - P))
        (r := ⟪P, m3sgnDir o (Q - P)⟫) hh
      rwa [hsub] at h2
    · intro hh
      exact m3_par_add_smul (u := m3sgnDir o (Q - P))
        (r := ⟪P, m3sgnDir o (Q - P)⟫) hh
  rw [hkey]
  exact (m3_par_par_iff (u := Q - P) (v := m3sgnDir o (Q - P)) hPQ hu
    (m3sgnDir_parallel (o := o) hPQ)).symm

theorem m3lineThrough_mem_left (P Q : E) (h : P ≠ Q) :
    (m3lineThrough (o := o) P Q h).mem P := by
  rw [m3lineThrough_mem_iff]
  exact ⟨0, by simp⟩

theorem m3lineThrough_mem_right (P Q : E) (h : P ≠ Q) :
    (m3lineThrough (o := o) P Q h).mem Q := by
  rw [m3lineThrough_mem_iff]
  exact ⟨1, (one_smul ℝ (Q - P)).symm⟩

theorem m3lineThrough_isCanonical (P Q : E) (h : P ≠ Q) :
    Line.isCanonical o (m3lineThrough (o := o) P Q h) := by
  have hPQ : Q - P ≠ 0 := sub_ne_zero.mpr h.symm
  have hnorm : ‖m3sgnDir o (Q - P)‖ = 1 := m3sgnDir_norm hPQ
  have hinner : ⟪P - ⟪P, m3sgnDir o (Q - P)⟫ • m3sgnDir o (Q - P),
      m3sgnDir o (Q - P)⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
    ring
  exact ⟨hnorm, hinner, m3sgnDir_sector hPQ⟩

/-- The canonical line through `P` and `Q` is exactly the affine line `P + ℝ • (Q - P)`
in the sense that any point on the `Line` `⟨P, Q - P⟩` lies on it. -/
theorem m3lineThrough_mem_of_mem_line (P Q : E) (h : P ≠ Q) {X : E}
    (hX : (⟨P, Q - P, sub_ne_zero.mpr h.symm⟩ : Line E).mem X) :
    (m3lineThrough (o := o) P Q h).mem X := by
  rw [m3lineThrough_mem_iff]
  exact (Line.mem_iff_parallel (⟨P, Q - P, sub_ne_zero.mpr h.symm⟩ : Line E) X).mp hX


theorem m3_par_neg_left_iff {u v : E} : Parallel (-u) v ↔ Parallel u v := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨-r, by rw [hr, smul_neg, neg_smul]⟩
  · rintro ⟨r, hr⟩
    exact ⟨-r, by rw [hr, smul_neg, neg_smul, neg_neg]⟩

/-- The canonical line and the raw line `P + ℝ • (Q - P)` have the same point set. -/
theorem m3lineThrough_mem_iff_raw (P Q : E) (h : P ≠ Q) (X : E) :
    (m3lineThrough (o := o) P Q h).mem X ↔
      (⟨P, Q - P, sub_ne_zero.mpr h.symm⟩ : Line E).mem X := by
  rw [m3lineThrough_mem_iff, Line.mem_iff_parallel]

/-- The raw lines `P + ℝ • (Q - P)` and `Q + ℝ • (P - Q)` have the same point set. -/
theorem m3_rawLine_comm (P Q : E) (h : P ≠ Q) (X : E) :
    (⟨P, Q - P, sub_ne_zero.mpr h.symm⟩ : Line E).mem X ↔
      (⟨Q, P - Q, sub_ne_zero.mpr h⟩ : Line E).mem X := by
  rw [Line.mem_iff_parallel, Line.mem_iff_parallel]
  have hsub : ∀ a : ℝ, a • (Q - P) - (Q - P) = (a - 1) • (Q - P) := by
    intro a
    rw [sub_smul, one_smul]
  have hneg : ∀ a : ℝ, (a - 1) • (Q - P) = (1 - a) • (P - Q) := by
    intro a
    rw [show P - Q = -(Q - P) from by abel, smul_neg, ← neg_smul]
    congr 1
    ring
  have hsub' : ∀ a : ℝ, a • (P - Q) - (P - Q) = (a - 1) • (P - Q) := by
    intro a
    rw [sub_smul, one_smul]
  have hneg' : ∀ a : ℝ, (a - 1) • (P - Q) = (1 - a) • (Q - P) := by
    intro a
    rw [show Q - P = -(P - Q) from by abel, smul_neg, ← neg_smul]
    congr 1
    ring
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨1 - a, ?_⟩
    rw [show X - Q = (X - P) - (Q - P) from by abel, ha, hsub, hneg]
  · rintro ⟨a, ha⟩
    refine ⟨1 - a, ?_⟩
    rw [show X - P = (X - Q) - (P - Q) from by abel, ha, hsub', hneg']

/-- The canonical line through two points does not depend on the order. -/
theorem m3lineThrough_comm (P Q : E) (h : P ≠ Q) :
    m3lineThrough (o := o) P Q h = m3lineThrough (o := o) Q P h.symm := by
  refine isCanonical_eq_of_mem_iff (m3lineThrough_isCanonical P Q h)
    (m3lineThrough_isCanonical Q P h.symm) ?_
  intro X
  rw [m3lineThrough_mem_iff_raw, m3lineThrough_mem_iff_raw]
  exact m3_rawLine_comm P Q h X

/-- Membership in the canonical line, with the parallel vector pointing the other way. -/
theorem m3lineThrough_mem_iff_swap (P Q : E) (h : P ≠ Q) (X : E) (hX : X ≠ P) :
    (m3lineThrough (o := o) P Q h).mem X ↔ Parallel (X - P) (Q - P) := by
  have hPQ : Q - P ≠ 0 := sub_ne_zero.mpr h.symm
  have hXu : X - P ≠ 0 := sub_ne_zero.mpr hX
  rw [m3lineThrough_mem_iff]
  exact ⟨fun hh => parallel_comm hPQ hXu hh, fun hh => parallel_comm hXu hPQ hh⟩

/-- Membership in the canonical line, with the parallel vector taken from the second point. -/
theorem m3lineThrough_mem_iff_swap' (P Q : E) (h : P ≠ Q) (X : E) (hX : X ≠ Q) :
    (m3lineThrough (o := o) P Q h).mem X ↔ Parallel (X - Q) (P - Q) := by
  rw [m3lineThrough_comm]
  exact m3lineThrough_mem_iff_swap Q P h.symm X hX

end OrientedTriangle
end XamboMorley
