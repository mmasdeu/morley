/-
  Member m3 (swarm smwh7aexl), direction d5: NINE_EXACT_GUIDE_MEMBERS.

  Part B (unconditional): the nine candidate guide lines as canonical `Line` values, with
  their direction in the Morley-side parallel class, their two red defining points, and the
  two green / two blue constellation points lying on each.  The 54 incidences are the
  compiled certificates of `.ultramath/smwh1zs5u/m2/M2P.lean` (copied verbatim into
  `inc/`), converted here into `Line.mem` form.  Nothing in this file is conditional.
-/
import M3A
import M2P

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

/-! ### Label-level helpers -/

theorem m3_cp_ne (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {q q' : ConstellationIndex} (hq : q ≠ q') :
    T.constellationPoint q ≠ T.constellationPoint q' :=
  fun hc => hq (h hc)

theorem m3_red_ne (T : OrientedTriangle E o) (h : Injective T.constellationPoint)
    {p q : TrisectorLabel × TrisectorLabel} (hpq : p ≠ q) :
    T.m5_redPt p ≠ T.m5_redPt q := by
  intro hc
  have hidx : (⟨.red, p.1, p.2⟩ : ConstellationIndex) = ⟨.red, q.1, q.2⟩ := h hc
  exact hpq (Prod.ext (congrArg ConstellationIndex.first hidx)
    (congrArg ConstellationIndex.second hidx))

theorem m3_side_ne_of_par (T : OrientedTriangle E o) (d : TrisectorLabel) {v : E}
    (hv : v ≠ 0) (h : Parallel (m3pSide T d) v) : m3pSide T d ≠ 0 := by
  rintro h0
  obtain ⟨r, hr⟩ := h
  rw [h0, smul_zero] at hr
  exact hv hr


/-! ### Line `m3LA0` — red pair `(0, 0)`, `(2, 1)`; side index `0` -/

noncomputable def m3LA0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Line E :=
  m3lineThrough (o := o) (T.m5_redPt ⟨0, 0⟩) (T.m5_redPt ⟨2, 1⟩)
    (m3_red_ne T h (by decide : (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨2, 1⟩))

theorem m3LA0_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA0 T h).mem (T.m5_redPt ⟨0, 0⟩) := by
  unfold m3LA0
  exact m3lineThrough_mem_left _ _ _

theorem m3LA0_far (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA0 T h).mem (T.m5_redPt ⟨2, 1⟩) := by
  unfold m3LA0
  exact m3lineThrough_mem_right _ _ _


theorem m3LA0_green_0_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA0 T h).mem (T.constellationPoint ⟨.green, 0, 0⟩) := by
  unfold m3LA0
  refine (m3lineThrough_mem_iff_swap (T.m5_redPt ⟨0, 0⟩) (T.m5_redPt ⟨2, 1⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 0, 0⟩ : ConstellationIndex) ≠ ⟨.red, 0, 0⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_000 T h)


theorem m3LA0_green_1_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA0 T h).mem (T.constellationPoint ⟨.green, 1, 2⟩) := by
  unfold m3LA0
  refine (m3lineThrough_mem_iff_swap' (T.m5_redPt ⟨0, 0⟩) (T.m5_redPt ⟨2, 1⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 1, 2⟩ : ConstellationIndex) ≠ ⟨.red, 2, 1⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_212 T h)


theorem m3LA0_blue_0_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA0 T h).mem (T.constellationPoint ⟨.blue, 0, 2⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 1, 2⟩ -
      T.constellationPoint ⟨.green, 0, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 1, 2⟩ : ConstellationIndex) ≠ ⟨.green, 0, 0⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 0, 0⟩,
      T.constellationPoint ⟨.green, 1, 2⟩ -
        T.constellationPoint ⟨.green, 0, 0⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 0, 2⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 0, 2⟩ : ConstellationIndex) ≠ ⟨.green, 0, 0⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_002 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 0, 0⟩,
      T.constellationPoint ⟨.green, 1, 2⟩ -
        T.constellationPoint ⟨.green, 0, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 0⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 0, 0⟩,
      T.constellationPoint ⟨.green, 1, 2⟩ -
        T.constellationPoint ⟨.green, 0, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 2⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 0, 0⟩ : ConstellationIndex) ≠ ⟨.green, 1, 2⟩))
    (m3LA0_green_0_0 T h) (m3LA0_green_1_2 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LA0_blue_2_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA0 T h).mem (T.constellationPoint ⟨.blue, 2, 0⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 0, 0⟩ -
      T.constellationPoint ⟨.green, 1, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 0, 0⟩ : ConstellationIndex) ≠ ⟨.green, 1, 2⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 1, 2⟩,
      T.constellationPoint ⟨.green, 0, 0⟩ -
        T.constellationPoint ⟨.green, 1, 2⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 2, 0⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 2, 0⟩ : ConstellationIndex) ≠ ⟨.green, 1, 2⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_120 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 1, 2⟩,
      T.constellationPoint ⟨.green, 0, 0⟩ -
        T.constellationPoint ⟨.green, 1, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 2⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 1, 2⟩,
      T.constellationPoint ⟨.green, 0, 0⟩ -
        T.constellationPoint ⟨.green, 1, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 0⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 1, 2⟩ : ConstellationIndex) ≠ ⟨.green, 0, 0⟩))
    (m3LA0_green_1_2 T h) (m3LA0_green_0_0 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LA0_side (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (m3pSide T (0 : TrisectorLabel)) (m3LA0 T h).direction := by
  have hpar := m3p_red_par31 T (0 : TrisectorLabel)
  have hpar' : Parallel (m3pSide T (0 : TrisectorLabel))
      (T.m5_redPt ⟨0, 0⟩ - T.m5_redPt ⟨2, 1⟩) := by
    simpa only [m5_redPt, show ((0 : TrisectorLabel) + 0) = 0 from by decide, show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] using hpar
  have hv : T.m5_redPt ⟨0, 0⟩ - T.m5_redPt ⟨2, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨2, 1⟩))
  have hqv : T.m5_redPt ⟨2, 1⟩ - T.m5_redPt ⟨0, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨0, 0⟩))
  have hside : m3pSide T (0 : TrisectorLabel) ≠ 0 := m3_side_ne_of_par T _ hv hpar'
  unfold m3LA0 m3lineThrough
  exact (m3_par_par_iff hside hv hpar').mpr (by
    simpa only [neg_sub] using m3_par_neg_left_iff.mpr (m3sgnDir_parallel hqv))

theorem m3LA0_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide (m3LA0 T h).direction :=
  m3p_side_ptM T (0 : TrisectorLabel) (m3LA0_side T h)


/-! ### Line `m3LB0` — red pair `(1, 2)`, `(0, 0)`; side index `2` -/

noncomputable def m3LB0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Line E :=
  m3lineThrough (o := o) (T.m5_redPt ⟨1, 2⟩) (T.m5_redPt ⟨0, 0⟩)
    (m3_red_ne T h (by decide : (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨0, 0⟩))

theorem m3LB0_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB0 T h).mem (T.m5_redPt ⟨1, 2⟩) := by
  unfold m3LB0
  exact m3lineThrough_mem_left _ _ _

theorem m3LB0_far (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB0 T h).mem (T.m5_redPt ⟨0, 0⟩) := by
  unfold m3LB0
  exact m3lineThrough_mem_right _ _ _


theorem m3LB0_green_0_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB0 T h).mem (T.constellationPoint ⟨.green, 0, 2⟩) := by
  unfold m3LB0
  refine (m3lineThrough_mem_iff_swap' (T.m5_redPt ⟨1, 2⟩) (T.m5_redPt ⟨0, 0⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 0, 2⟩ : ConstellationIndex) ≠ ⟨.red, 0, 0⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_002 T h)


theorem m3LB0_green_2_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB0 T h).mem (T.constellationPoint ⟨.green, 2, 0⟩) := by
  unfold m3LB0
  refine (m3lineThrough_mem_iff_swap (T.m5_redPt ⟨1, 2⟩) (T.m5_redPt ⟨0, 0⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 2, 0⟩ : ConstellationIndex) ≠ ⟨.red, 1, 2⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_120 T h)


theorem m3LB0_blue_0_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB0 T h).mem (T.constellationPoint ⟨.blue, 0, 0⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 0, 2⟩ -
      T.constellationPoint ⟨.green, 2, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 0, 2⟩ : ConstellationIndex) ≠ ⟨.green, 2, 0⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 2, 0⟩,
      T.constellationPoint ⟨.green, 0, 2⟩ -
        T.constellationPoint ⟨.green, 2, 0⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 0, 0⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 0, 0⟩ : ConstellationIndex) ≠ ⟨.green, 2, 0⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_200 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 2, 0⟩,
      T.constellationPoint ⟨.green, 0, 2⟩ -
        T.constellationPoint ⟨.green, 2, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 0⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 2, 0⟩,
      T.constellationPoint ⟨.green, 0, 2⟩ -
        T.constellationPoint ⟨.green, 2, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 2⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 2, 0⟩ : ConstellationIndex) ≠ ⟨.green, 0, 2⟩))
    (m3LB0_green_2_0 T h) (m3LB0_green_0_2 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LB0_blue_2_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB0 T h).mem (T.constellationPoint ⟨.blue, 2, 1⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 2, 0⟩ -
      T.constellationPoint ⟨.green, 0, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 2, 0⟩ : ConstellationIndex) ≠ ⟨.green, 0, 2⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 0, 2⟩,
      T.constellationPoint ⟨.green, 2, 0⟩ -
        T.constellationPoint ⟨.green, 0, 2⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 2, 1⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 2, 1⟩ : ConstellationIndex) ≠ ⟨.green, 0, 2⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_021 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 0, 2⟩,
      T.constellationPoint ⟨.green, 2, 0⟩ -
        T.constellationPoint ⟨.green, 0, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 2⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 0, 2⟩,
      T.constellationPoint ⟨.green, 2, 0⟩ -
        T.constellationPoint ⟨.green, 0, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 0⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 0, 2⟩ : ConstellationIndex) ≠ ⟨.green, 2, 0⟩))
    (m3LB0_green_0_2 T h) (m3LB0_green_2_0 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LB0_side (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (m3pSide T (2 : TrisectorLabel)) (m3LB0 T h).direction := by
  have hpar := m3p_red_par12 T (0 : TrisectorLabel)
  have hpar' : Parallel (m3pSide T (2 : TrisectorLabel))
      (T.m5_redPt ⟨1, 2⟩ - T.m5_redPt ⟨0, 0⟩) := by
    simpa only [m5_redPt, show ((0 : TrisectorLabel) + 0) = 0 from by decide, show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] using hpar
  have hv : T.m5_redPt ⟨1, 2⟩ - T.m5_redPt ⟨0, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨0, 0⟩))
  have hqv : T.m5_redPt ⟨0, 0⟩ - T.m5_redPt ⟨1, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨0, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨1, 2⟩))
  have hside : m3pSide T (2 : TrisectorLabel) ≠ 0 := m3_side_ne_of_par T _ hv hpar'
  unfold m3LB0 m3lineThrough
  exact (m3_par_par_iff hside hv hpar').mpr (by
    simpa only [neg_sub] using m3_par_neg_left_iff.mpr (m3sgnDir_parallel hqv))

theorem m3LB0_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide (m3LB0 T h).direction :=
  m3p_side_ptM T (2 : TrisectorLabel) (m3LB0_side T h)


/-! ### Line `m3LA1` — red pair `(1, 0)`, `(0, 1)`; side index `1` -/

noncomputable def m3LA1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Line E :=
  m3lineThrough (o := o) (T.m5_redPt ⟨1, 0⟩) (T.m5_redPt ⟨0, 1⟩)
    (m3_red_ne T h (by decide : (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨0, 1⟩))

theorem m3LA1_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA1 T h).mem (T.m5_redPt ⟨1, 0⟩) := by
  unfold m3LA1
  exact m3lineThrough_mem_left _ _ _

theorem m3LA1_far (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA1 T h).mem (T.m5_redPt ⟨0, 1⟩) := by
  unfold m3LA1
  exact m3lineThrough_mem_right _ _ _


theorem m3LA1_green_0_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA1 T h).mem (T.constellationPoint ⟨.green, 0, 2⟩) := by
  unfold m3LA1
  refine (m3lineThrough_mem_iff_swap (T.m5_redPt ⟨1, 0⟩) (T.m5_redPt ⟨0, 1⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 0, 2⟩ : ConstellationIndex) ≠ ⟨.red, 1, 0⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_102 T h)


theorem m3LA1_green_1_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA1 T h).mem (T.constellationPoint ⟨.green, 1, 1⟩) := by
  unfold m3LA1
  refine (m3lineThrough_mem_iff_swap' (T.m5_redPt ⟨1, 0⟩) (T.m5_redPt ⟨0, 1⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 1, 1⟩ : ConstellationIndex) ≠ ⟨.red, 0, 1⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_011 T h)


theorem m3LA1_blue_1_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA1 T h).mem (T.constellationPoint ⟨.blue, 1, 1⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 0, 2⟩ -
      T.constellationPoint ⟨.green, 1, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 0, 2⟩ : ConstellationIndex) ≠ ⟨.green, 1, 1⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 1, 1⟩,
      T.constellationPoint ⟨.green, 0, 2⟩ -
        T.constellationPoint ⟨.green, 1, 1⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 1, 1⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 1, 1⟩ : ConstellationIndex) ≠ ⟨.green, 1, 1⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_111 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 1, 1⟩,
      T.constellationPoint ⟨.green, 0, 2⟩ -
        T.constellationPoint ⟨.green, 1, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 1⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 1, 1⟩,
      T.constellationPoint ⟨.green, 0, 2⟩ -
        T.constellationPoint ⟨.green, 1, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 2⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 1, 1⟩ : ConstellationIndex) ≠ ⟨.green, 0, 2⟩))
    (m3LA1_green_1_1 T h) (m3LA1_green_0_2 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LA1_blue_2_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA1 T h).mem (T.constellationPoint ⟨.blue, 2, 0⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 1, 1⟩ -
      T.constellationPoint ⟨.green, 0, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 1, 1⟩ : ConstellationIndex) ≠ ⟨.green, 0, 2⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 0, 2⟩,
      T.constellationPoint ⟨.green, 1, 1⟩ -
        T.constellationPoint ⟨.green, 0, 2⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 2, 0⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 2, 0⟩ : ConstellationIndex) ≠ ⟨.green, 0, 2⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_020 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 0, 2⟩,
      T.constellationPoint ⟨.green, 1, 1⟩ -
        T.constellationPoint ⟨.green, 0, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 2⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 0, 2⟩,
      T.constellationPoint ⟨.green, 1, 1⟩ -
        T.constellationPoint ⟨.green, 0, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 1⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 0, 2⟩ : ConstellationIndex) ≠ ⟨.green, 1, 1⟩))
    (m3LA1_green_0_2 T h) (m3LA1_green_1_1 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LA1_side (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (m3pSide T (1 : TrisectorLabel)) (m3LA1 T h).direction := by
  have hpar := m3p_red_par31 T (1 : TrisectorLabel)
  have hpar' : Parallel (m3pSide T (1 : TrisectorLabel))
      (T.m5_redPt ⟨1, 0⟩ - T.m5_redPt ⟨0, 1⟩) := by
    simpa only [m5_redPt, show ((1 : TrisectorLabel) + 0) = 1 from by decide, show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] using hpar
  have hv : T.m5_redPt ⟨1, 0⟩ - T.m5_redPt ⟨0, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨0, 1⟩))
  have hqv : T.m5_redPt ⟨0, 1⟩ - T.m5_redPt ⟨1, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨1, 0⟩))
  have hside : m3pSide T (1 : TrisectorLabel) ≠ 0 := m3_side_ne_of_par T _ hv hpar'
  unfold m3LA1 m3lineThrough
  exact (m3_par_par_iff hside hv hpar').mpr (by
    simpa only [neg_sub] using m3_par_neg_left_iff.mpr (m3sgnDir_parallel hqv))

theorem m3LA1_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide (m3LA1 T h).direction :=
  m3p_side_ptM T (1 : TrisectorLabel) (m3LA1_side T h)


/-! ### Line `m3LC1` — red pair `(0, 1)`, `(2, 2)`; side index `2` -/

noncomputable def m3LC1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Line E :=
  m3lineThrough (o := o) (T.m5_redPt ⟨0, 1⟩) (T.m5_redPt ⟨2, 2⟩)
    (m3_red_ne T h (by decide : (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨2, 2⟩))

theorem m3LC1_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC1 T h).mem (T.m5_redPt ⟨0, 1⟩) := by
  unfold m3LC1
  exact m3lineThrough_mem_left _ _ _

theorem m3LC1_far (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC1 T h).mem (T.m5_redPt ⟨2, 2⟩) := by
  unfold m3LC1
  exact m3lineThrough_mem_right _ _ _


theorem m3LC1_green_1_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC1 T h).mem (T.constellationPoint ⟨.green, 1, 2⟩) := by
  unfold m3LC1
  refine (m3lineThrough_mem_iff_swap (T.m5_redPt ⟨0, 1⟩) (T.m5_redPt ⟨2, 2⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 1, 2⟩ : ConstellationIndex) ≠ ⟨.red, 0, 1⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_012 T h)


theorem m3LC1_green_2_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC1 T h).mem (T.constellationPoint ⟨.green, 2, 1⟩) := by
  unfold m3LC1
  refine (m3lineThrough_mem_iff_swap' (T.m5_redPt ⟨0, 1⟩) (T.m5_redPt ⟨2, 2⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 2, 1⟩ : ConstellationIndex) ≠ ⟨.red, 2, 2⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_221 T h)


theorem m3LC1_blue_1_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC1 T h).mem (T.constellationPoint ⟨.blue, 1, 0⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 1, 2⟩ -
      T.constellationPoint ⟨.green, 2, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 1, 2⟩ : ConstellationIndex) ≠ ⟨.green, 2, 1⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 2, 1⟩,
      T.constellationPoint ⟨.green, 1, 2⟩ -
        T.constellationPoint ⟨.green, 2, 1⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 1, 0⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 1, 0⟩ : ConstellationIndex) ≠ ⟨.green, 2, 1⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_210 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 2, 1⟩,
      T.constellationPoint ⟨.green, 1, 2⟩ -
        T.constellationPoint ⟨.green, 2, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 1⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 2, 1⟩,
      T.constellationPoint ⟨.green, 1, 2⟩ -
        T.constellationPoint ⟨.green, 2, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 2⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 2, 1⟩ : ConstellationIndex) ≠ ⟨.green, 1, 2⟩))
    (m3LC1_green_2_1 T h) (m3LC1_green_1_2 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LC1_blue_2_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC1 T h).mem (T.constellationPoint ⟨.blue, 2, 2⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 2, 1⟩ -
      T.constellationPoint ⟨.green, 1, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 2, 1⟩ : ConstellationIndex) ≠ ⟨.green, 1, 2⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 1, 2⟩,
      T.constellationPoint ⟨.green, 2, 1⟩ -
        T.constellationPoint ⟨.green, 1, 2⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 2, 2⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 2, 2⟩ : ConstellationIndex) ≠ ⟨.green, 1, 2⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_122 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 1, 2⟩,
      T.constellationPoint ⟨.green, 2, 1⟩ -
        T.constellationPoint ⟨.green, 1, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 2⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 1, 2⟩,
      T.constellationPoint ⟨.green, 2, 1⟩ -
        T.constellationPoint ⟨.green, 1, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 1⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 1, 2⟩ : ConstellationIndex) ≠ ⟨.green, 2, 1⟩))
    (m3LC1_green_1_2 T h) (m3LC1_green_2_1 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LC1_side (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (m3pSide T (2 : TrisectorLabel)) (m3LC1 T h).direction := by
  have hpar := m3p_red_par23 T (1 : TrisectorLabel)
  have hpar' : Parallel (m3pSide T (2 : TrisectorLabel))
      (T.m5_redPt ⟨0, 1⟩ - T.m5_redPt ⟨2, 2⟩) := by
    simpa only [m5_redPt, show ((1 : TrisectorLabel) + 0) = 1 from by decide, show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] using hpar
  have hv : T.m5_redPt ⟨0, 1⟩ - T.m5_redPt ⟨2, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨0, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨2, 2⟩))
  have hqv : T.m5_redPt ⟨2, 2⟩ - T.m5_redPt ⟨0, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨0, 1⟩))
  have hside : m3pSide T (2 : TrisectorLabel) ≠ 0 := m3_side_ne_of_par T _ hv hpar'
  unfold m3LC1 m3lineThrough
  exact (m3_par_par_iff hside hv hpar').mpr (by
    simpa only [neg_sub] using m3_par_neg_left_iff.mpr (m3sgnDir_parallel hqv))

theorem m3LC1_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide (m3LC1 T h).direction :=
  m3p_side_ptM T (2 : TrisectorLabel) (m3LC1_side T h)


/-! ### Line `m3LC2` — red pair `(1, 1)`, `(0, 2)`; side index `0` -/

noncomputable def m3LC2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Line E :=
  m3lineThrough (o := o) (T.m5_redPt ⟨1, 1⟩) (T.m5_redPt ⟨0, 2⟩)
    (m3_red_ne T h (by decide : (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨0, 2⟩))

theorem m3LC2_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC2 T h).mem (T.m5_redPt ⟨1, 1⟩) := by
  unfold m3LC2
  exact m3lineThrough_mem_left _ _ _

theorem m3LC2_far (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC2 T h).mem (T.m5_redPt ⟨0, 2⟩) := by
  unfold m3LC2
  exact m3lineThrough_mem_right _ _ _


theorem m3LC2_green_1_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC2 T h).mem (T.constellationPoint ⟨.green, 1, 1⟩) := by
  unfold m3LC2
  refine (m3lineThrough_mem_iff_swap (T.m5_redPt ⟨1, 1⟩) (T.m5_redPt ⟨0, 2⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 1, 1⟩ : ConstellationIndex) ≠ ⟨.red, 1, 1⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_111 T h)


theorem m3LC2_green_2_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC2 T h).mem (T.constellationPoint ⟨.green, 2, 0⟩) := by
  unfold m3LC2
  refine (m3lineThrough_mem_iff_swap' (T.m5_redPt ⟨1, 1⟩) (T.m5_redPt ⟨0, 2⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 2, 0⟩ : ConstellationIndex) ≠ ⟨.red, 0, 2⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_020 T h)


theorem m3LC2_blue_0_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC2 T h).mem (T.constellationPoint ⟨.blue, 0, 1⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 1, 1⟩ -
      T.constellationPoint ⟨.green, 2, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 1, 1⟩ : ConstellationIndex) ≠ ⟨.green, 2, 0⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 2, 0⟩,
      T.constellationPoint ⟨.green, 1, 1⟩ -
        T.constellationPoint ⟨.green, 2, 0⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 0, 1⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 0, 1⟩ : ConstellationIndex) ≠ ⟨.green, 2, 0⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_201 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 2, 0⟩,
      T.constellationPoint ⟨.green, 1, 1⟩ -
        T.constellationPoint ⟨.green, 2, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 0⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 2, 0⟩,
      T.constellationPoint ⟨.green, 1, 1⟩ -
        T.constellationPoint ⟨.green, 2, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 1⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 2, 0⟩ : ConstellationIndex) ≠ ⟨.green, 1, 1⟩))
    (m3LC2_green_2_0 T h) (m3LC2_green_1_1 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LC2_blue_1_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC2 T h).mem (T.constellationPoint ⟨.blue, 1, 0⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 2, 0⟩ -
      T.constellationPoint ⟨.green, 1, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 2, 0⟩ : ConstellationIndex) ≠ ⟨.green, 1, 1⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 1, 1⟩,
      T.constellationPoint ⟨.green, 2, 0⟩ -
        T.constellationPoint ⟨.green, 1, 1⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 1, 0⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 1, 0⟩ : ConstellationIndex) ≠ ⟨.green, 1, 1⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_110 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 1, 1⟩,
      T.constellationPoint ⟨.green, 2, 0⟩ -
        T.constellationPoint ⟨.green, 1, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 1⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 1, 1⟩,
      T.constellationPoint ⟨.green, 2, 0⟩ -
        T.constellationPoint ⟨.green, 1, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 0⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 1, 1⟩ : ConstellationIndex) ≠ ⟨.green, 2, 0⟩))
    (m3LC2_green_1_1 T h) (m3LC2_green_2_0 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LC2_side (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (m3pSide T (0 : TrisectorLabel)) (m3LC2 T h).direction := by
  have hpar := m3p_red_par23 T (2 : TrisectorLabel)
  have hpar' : Parallel (m3pSide T (0 : TrisectorLabel))
      (T.m5_redPt ⟨1, 1⟩ - T.m5_redPt ⟨0, 2⟩) := by
    simpa only [m5_redPt, show ((2 : TrisectorLabel) + 0) = 2 from by decide, show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] using hpar
  have hv : T.m5_redPt ⟨1, 1⟩ - T.m5_redPt ⟨0, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨0, 2⟩))
  have hqv : T.m5_redPt ⟨0, 2⟩ - T.m5_redPt ⟨1, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨1, 1⟩))
  have hside : m3pSide T (0 : TrisectorLabel) ≠ 0 := m3_side_ne_of_par T _ hv hpar'
  unfold m3LC2 m3lineThrough
  exact (m3_par_par_iff hside hv hpar').mpr (by
    simpa only [neg_sub] using m3_par_neg_left_iff.mpr (m3sgnDir_parallel hqv))

theorem m3LC2_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide (m3LC2 T h).direction :=
  m3p_side_ptM T (0 : TrisectorLabel) (m3LC2_side T h)


/-! ### Line `m3LB2` — red pair `(0, 2)`, `(2, 0)`; side index `1` -/

noncomputable def m3LB2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Line E :=
  m3lineThrough (o := o) (T.m5_redPt ⟨0, 2⟩) (T.m5_redPt ⟨2, 0⟩)
    (m3_red_ne T h (by decide : (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨2, 0⟩))

theorem m3LB2_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB2 T h).mem (T.m5_redPt ⟨0, 2⟩) := by
  unfold m3LB2
  exact m3lineThrough_mem_left _ _ _

theorem m3LB2_far (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB2 T h).mem (T.m5_redPt ⟨2, 0⟩) := by
  unfold m3LB2
  exact m3lineThrough_mem_right _ _ _


theorem m3LB2_green_0_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB2 T h).mem (T.constellationPoint ⟨.green, 0, 0⟩) := by
  unfold m3LB2
  refine (m3lineThrough_mem_iff_swap' (T.m5_redPt ⟨0, 2⟩) (T.m5_redPt ⟨2, 0⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 0, 0⟩ : ConstellationIndex) ≠ ⟨.red, 2, 0⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_200 T h)


theorem m3LB2_green_2_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB2 T h).mem (T.constellationPoint ⟨.green, 2, 1⟩) := by
  unfold m3LB2
  refine (m3lineThrough_mem_iff_swap (T.m5_redPt ⟨0, 2⟩) (T.m5_redPt ⟨2, 0⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 2, 1⟩ : ConstellationIndex) ≠ ⟨.red, 0, 2⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_021 T h)


theorem m3LB2_blue_0_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB2 T h).mem (T.constellationPoint ⟨.blue, 0, 0⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 2, 1⟩ -
      T.constellationPoint ⟨.green, 0, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 2, 1⟩ : ConstellationIndex) ≠ ⟨.green, 0, 0⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 0, 0⟩,
      T.constellationPoint ⟨.green, 2, 1⟩ -
        T.constellationPoint ⟨.green, 0, 0⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 0, 0⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 0, 0⟩ : ConstellationIndex) ≠ ⟨.green, 0, 0⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_000 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 0, 0⟩,
      T.constellationPoint ⟨.green, 2, 1⟩ -
        T.constellationPoint ⟨.green, 0, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 0⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 0, 0⟩,
      T.constellationPoint ⟨.green, 2, 1⟩ -
        T.constellationPoint ⟨.green, 0, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 1⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 0, 0⟩ : ConstellationIndex) ≠ ⟨.green, 2, 1⟩))
    (m3LB2_green_0_0 T h) (m3LB2_green_2_1 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LB2_blue_1_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB2 T h).mem (T.constellationPoint ⟨.blue, 1, 2⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 0, 0⟩ -
      T.constellationPoint ⟨.green, 2, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 0, 0⟩ : ConstellationIndex) ≠ ⟨.green, 2, 1⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 2, 1⟩,
      T.constellationPoint ⟨.green, 0, 0⟩ -
        T.constellationPoint ⟨.green, 2, 1⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 1, 2⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 1, 2⟩ : ConstellationIndex) ≠ ⟨.green, 2, 1⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_212 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 2, 1⟩,
      T.constellationPoint ⟨.green, 0, 0⟩ -
        T.constellationPoint ⟨.green, 2, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 1⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 2, 1⟩,
      T.constellationPoint ⟨.green, 0, 0⟩ -
        T.constellationPoint ⟨.green, 2, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 0⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 2, 1⟩ : ConstellationIndex) ≠ ⟨.green, 0, 0⟩))
    (m3LB2_green_2_1 T h) (m3LB2_green_0_0 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LB2_side (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (m3pSide T (1 : TrisectorLabel)) (m3LB2 T h).direction := by
  have hpar := m3p_red_par12 T (2 : TrisectorLabel)
  have hpar' : Parallel (m3pSide T (1 : TrisectorLabel))
      (T.m5_redPt ⟨0, 2⟩ - T.m5_redPt ⟨2, 0⟩) := by
    simpa only [m5_redPt, show ((2 : TrisectorLabel) + 0) = 2 from by decide, show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] using hpar
  have hv : T.m5_redPt ⟨0, 2⟩ - T.m5_redPt ⟨2, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨0, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨2, 0⟩))
  have hqv : T.m5_redPt ⟨2, 0⟩ - T.m5_redPt ⟨0, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨0, 2⟩))
  have hside : m3pSide T (1 : TrisectorLabel) ≠ 0 := m3_side_ne_of_par T _ hv hpar'
  unfold m3LB2 m3lineThrough
  exact (m3_par_par_iff hside hv hpar').mpr (by
    simpa only [neg_sub] using m3_par_neg_left_iff.mpr (m3sgnDir_parallel hqv))

theorem m3LB2_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide (m3LB2 T h).direction :=
  m3p_side_ptM T (1 : TrisectorLabel) (m3LB2_side T h)


/-! ### Line `m3LB1` — red pair `(2, 2)`, `(1, 0)`; side index `0` -/

noncomputable def m3LB1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Line E :=
  m3lineThrough (o := o) (T.m5_redPt ⟨2, 2⟩) (T.m5_redPt ⟨1, 0⟩)
    (m3_red_ne T h (by decide : (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨1, 0⟩))

theorem m3LB1_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB1 T h).mem (T.m5_redPt ⟨2, 2⟩) := by
  unfold m3LB1
  exact m3lineThrough_mem_left _ _ _

theorem m3LB1_far (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB1 T h).mem (T.m5_redPt ⟨1, 0⟩) := by
  unfold m3LB1
  exact m3lineThrough_mem_right _ _ _


theorem m3LB1_green_0_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB1 T h).mem (T.constellationPoint ⟨.green, 0, 1⟩) := by
  unfold m3LB1
  refine (m3lineThrough_mem_iff_swap' (T.m5_redPt ⟨2, 2⟩) (T.m5_redPt ⟨1, 0⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 0, 1⟩ : ConstellationIndex) ≠ ⟨.red, 1, 0⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_101 T h)


theorem m3LB1_green_2_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB1 T h).mem (T.constellationPoint ⟨.green, 2, 2⟩) := by
  unfold m3LB1
  refine (m3lineThrough_mem_iff_swap (T.m5_redPt ⟨2, 2⟩) (T.m5_redPt ⟨1, 0⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 2, 2⟩ : ConstellationIndex) ≠ ⟨.red, 2, 2⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_222 T h)


theorem m3LB1_blue_1_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB1 T h).mem (T.constellationPoint ⟨.blue, 1, 2⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 2, 2⟩ -
      T.constellationPoint ⟨.green, 0, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 2, 2⟩ : ConstellationIndex) ≠ ⟨.green, 0, 1⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 0, 1⟩,
      T.constellationPoint ⟨.green, 2, 2⟩ -
        T.constellationPoint ⟨.green, 0, 1⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 1, 2⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 1, 2⟩ : ConstellationIndex) ≠ ⟨.green, 0, 1⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_012 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 0, 1⟩,
      T.constellationPoint ⟨.green, 2, 2⟩ -
        T.constellationPoint ⟨.green, 0, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 1⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 0, 1⟩,
      T.constellationPoint ⟨.green, 2, 2⟩ -
        T.constellationPoint ⟨.green, 0, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 2⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 0, 1⟩ : ConstellationIndex) ≠ ⟨.green, 2, 2⟩))
    (m3LB1_green_0_1 T h) (m3LB1_green_2_2 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LB1_blue_2_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LB1 T h).mem (T.constellationPoint ⟨.blue, 2, 1⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 0, 1⟩ -
      T.constellationPoint ⟨.green, 2, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 0, 1⟩ : ConstellationIndex) ≠ ⟨.green, 2, 2⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 2, 2⟩,
      T.constellationPoint ⟨.green, 0, 1⟩ -
        T.constellationPoint ⟨.green, 2, 2⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 2, 1⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 2, 1⟩ : ConstellationIndex) ≠ ⟨.green, 2, 2⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_221 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 2, 2⟩,
      T.constellationPoint ⟨.green, 0, 1⟩ -
        T.constellationPoint ⟨.green, 2, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 2⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 2, 2⟩,
      T.constellationPoint ⟨.green, 0, 1⟩ -
        T.constellationPoint ⟨.green, 2, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 1⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 2, 2⟩ : ConstellationIndex) ≠ ⟨.green, 0, 1⟩))
    (m3LB1_green_2_2 T h) (m3LB1_green_0_1 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LB1_side (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (m3pSide T (0 : TrisectorLabel)) (m3LB1 T h).direction := by
  have hpar := m3p_red_par12 T (1 : TrisectorLabel)
  have hpar' : Parallel (m3pSide T (0 : TrisectorLabel))
      (T.m5_redPt ⟨2, 2⟩ - T.m5_redPt ⟨1, 0⟩) := by
    simpa only [m5_redPt, show ((1 : TrisectorLabel) + 0) = 1 from by decide, show ((1 : TrisectorLabel) + 1) = 2 from by decide, show ((1 : TrisectorLabel) + 2) = 0 from by decide] using hpar
  have hv : T.m5_redPt ⟨2, 2⟩ - T.m5_redPt ⟨1, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨2, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨1, 0⟩))
  have hqv : T.m5_redPt ⟨1, 0⟩ - T.m5_redPt ⟨2, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨1, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨2, 2⟩))
  have hside : m3pSide T (0 : TrisectorLabel) ≠ 0 := m3_side_ne_of_par T _ hv hpar'
  unfold m3LB1 m3lineThrough
  exact (m3_par_par_iff hside hv hpar').mpr (by
    simpa only [neg_sub] using m3_par_neg_left_iff.mpr (m3sgnDir_parallel hqv))

theorem m3LB1_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide (m3LB1 T h).direction :=
  m3p_side_ptM T (0 : TrisectorLabel) (m3LB1_side T h)


/-! ### Line `m3LA2` — red pair `(2, 0)`, `(1, 1)`; side index `2` -/

noncomputable def m3LA2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Line E :=
  m3lineThrough (o := o) (T.m5_redPt ⟨2, 0⟩) (T.m5_redPt ⟨1, 1⟩)
    (m3_red_ne T h (by decide : (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨1, 1⟩))

theorem m3LA2_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA2 T h).mem (T.m5_redPt ⟨2, 0⟩) := by
  unfold m3LA2
  exact m3lineThrough_mem_left _ _ _

theorem m3LA2_far (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA2 T h).mem (T.m5_redPt ⟨1, 1⟩) := by
  unfold m3LA2
  exact m3lineThrough_mem_right _ _ _


theorem m3LA2_green_0_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA2 T h).mem (T.constellationPoint ⟨.green, 0, 1⟩) := by
  unfold m3LA2
  refine (m3lineThrough_mem_iff_swap (T.m5_redPt ⟨2, 0⟩) (T.m5_redPt ⟨1, 1⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 0, 1⟩ : ConstellationIndex) ≠ ⟨.red, 2, 0⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_201 T h)


theorem m3LA2_green_1_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA2 T h).mem (T.constellationPoint ⟨.green, 1, 0⟩) := by
  unfold m3LA2
  refine (m3lineThrough_mem_iff_swap' (T.m5_redPt ⟨2, 0⟩) (T.m5_redPt ⟨1, 1⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 1, 0⟩ : ConstellationIndex) ≠ ⟨.red, 1, 1⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_110 T h)


theorem m3LA2_blue_0_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA2 T h).mem (T.constellationPoint ⟨.blue, 0, 2⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 0, 1⟩ -
      T.constellationPoint ⟨.green, 1, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 0, 1⟩ : ConstellationIndex) ≠ ⟨.green, 1, 0⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 1, 0⟩,
      T.constellationPoint ⟨.green, 0, 1⟩ -
        T.constellationPoint ⟨.green, 1, 0⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 0, 2⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 0, 2⟩ : ConstellationIndex) ≠ ⟨.green, 1, 0⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_102 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 1, 0⟩,
      T.constellationPoint ⟨.green, 0, 1⟩ -
        T.constellationPoint ⟨.green, 1, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 0⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 1, 0⟩,
      T.constellationPoint ⟨.green, 0, 1⟩ -
        T.constellationPoint ⟨.green, 1, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 1⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 1, 0⟩ : ConstellationIndex) ≠ ⟨.green, 0, 1⟩))
    (m3LA2_green_1_0 T h) (m3LA2_green_0_1 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LA2_blue_1_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LA2 T h).mem (T.constellationPoint ⟨.blue, 1, 1⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 1, 0⟩ -
      T.constellationPoint ⟨.green, 0, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 1, 0⟩ : ConstellationIndex) ≠ ⟨.green, 0, 1⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 0, 1⟩,
      T.constellationPoint ⟨.green, 1, 0⟩ -
        T.constellationPoint ⟨.green, 0, 1⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 1, 1⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 1, 1⟩ : ConstellationIndex) ≠ ⟨.green, 0, 1⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_011 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 0, 1⟩,
      T.constellationPoint ⟨.green, 1, 0⟩ -
        T.constellationPoint ⟨.green, 0, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 0, 1⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 0, 1⟩,
      T.constellationPoint ⟨.green, 1, 0⟩ -
        T.constellationPoint ⟨.green, 0, 1⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 0⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 0, 1⟩ : ConstellationIndex) ≠ ⟨.green, 1, 0⟩))
    (m3LA2_green_0_1 T h) (m3LA2_green_1_0 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LA2_side (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (m3pSide T (2 : TrisectorLabel)) (m3LA2 T h).direction := by
  have hpar := m3p_red_par31 T (2 : TrisectorLabel)
  have hpar' : Parallel (m3pSide T (2 : TrisectorLabel))
      (T.m5_redPt ⟨2, 0⟩ - T.m5_redPt ⟨1, 1⟩) := by
    simpa only [m5_redPt, show ((2 : TrisectorLabel) + 0) = 2 from by decide, show ((2 : TrisectorLabel) + 1) = 0 from by decide, show ((2 : TrisectorLabel) + 2) = 1 from by decide] using hpar
  have hv : T.m5_redPt ⟨2, 0⟩ - T.m5_redPt ⟨1, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨2, 0⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨1, 1⟩))
  have hqv : T.m5_redPt ⟨1, 1⟩ - T.m5_redPt ⟨2, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨1, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨2, 0⟩))
  have hside : m3pSide T (2 : TrisectorLabel) ≠ 0 := m3_side_ne_of_par T _ hv hpar'
  unfold m3LA2 m3lineThrough
  exact (m3_par_par_iff hside hv hpar').mpr (by
    simpa only [neg_sub] using m3_par_neg_left_iff.mpr (m3sgnDir_parallel hqv))

theorem m3LA2_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide (m3LA2 T h).direction :=
  m3p_side_ptM T (2 : TrisectorLabel) (m3LA2_side T h)


/-! ### Line `m3LC0` — red pair `(2, 1)`, `(1, 2)`; side index `1` -/

noncomputable def m3LC0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Line E :=
  m3lineThrough (o := o) (T.m5_redPt ⟨2, 1⟩) (T.m5_redPt ⟨1, 2⟩)
    (m3_red_ne T h (by decide : (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨1, 2⟩))

theorem m3LC0_base (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC0 T h).mem (T.m5_redPt ⟨2, 1⟩) := by
  unfold m3LC0
  exact m3lineThrough_mem_left _ _ _

theorem m3LC0_far (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC0 T h).mem (T.m5_redPt ⟨1, 2⟩) := by
  unfold m3LC0
  exact m3lineThrough_mem_right _ _ _


theorem m3LC0_green_1_0 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC0 T h).mem (T.constellationPoint ⟨.green, 1, 0⟩) := by
  unfold m3LC0
  refine (m3lineThrough_mem_iff_swap (T.m5_redPt ⟨2, 1⟩) (T.m5_redPt ⟨1, 2⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 1, 0⟩ : ConstellationIndex) ≠ ⟨.red, 2, 1⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_210 T h)


theorem m3LC0_green_2_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC0 T h).mem (T.constellationPoint ⟨.green, 2, 2⟩) := by
  unfold m3LC0
  refine (m3lineThrough_mem_iff_swap' (T.m5_redPt ⟨2, 1⟩) (T.m5_redPt ⟨1, 2⟩) _ _
    (m3_cp_ne T h (by decide :
      (⟨.green, 2, 2⟩ : ConstellationIndex) ≠ ⟨.red, 1, 2⟩))).mpr ?_
  exact m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_par_122 T h)


theorem m3LC0_blue_0_1 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC0 T h).mem (T.constellationPoint ⟨.blue, 0, 1⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 2, 2⟩ -
      T.constellationPoint ⟨.green, 1, 0⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 2, 2⟩ : ConstellationIndex) ≠ ⟨.green, 1, 0⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 1, 0⟩,
      T.constellationPoint ⟨.green, 2, 2⟩ -
        T.constellationPoint ⟨.green, 1, 0⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 0, 1⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 0, 1⟩ : ConstellationIndex) ≠ ⟨.green, 1, 0⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_101 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 1, 0⟩,
      T.constellationPoint ⟨.green, 2, 2⟩ -
        T.constellationPoint ⟨.green, 1, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 0⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 1, 0⟩,
      T.constellationPoint ⟨.green, 2, 2⟩ -
        T.constellationPoint ⟨.green, 1, 0⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 2⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 1, 0⟩ : ConstellationIndex) ≠ ⟨.green, 2, 2⟩))
    (m3LC0_green_1_0 T h) (m3LC0_green_2_2 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LC0_blue_2_2 (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    (m3LC0 T h).mem (T.constellationPoint ⟨.blue, 2, 2⟩) := by
  have hdirne : T.constellationPoint ⟨.green, 1, 0⟩ -
      T.constellationPoint ⟨.green, 2, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_cp_ne T h (by decide :
      (⟨.green, 1, 0⟩ : ConstellationIndex) ≠ ⟨.green, 2, 2⟩))
  have hG : (⟨T.constellationPoint ⟨.green, 2, 2⟩,
      T.constellationPoint ⟨.green, 1, 0⟩ -
        T.constellationPoint ⟨.green, 2, 2⟩,
      hdirne⟩ : Line E).mem
      (T.constellationPoint ⟨.blue, 2, 2⟩) := by
    rw [Line.mem_iff_parallel]
    exact parallel_comm (sub_ne_zero.mpr (m3_cp_ne T h (by decide :
        (⟨.blue, 2, 2⟩ : ConstellationIndex) ≠ ⟨.green, 2, 2⟩))) hdirne
      (m3_par_neg_right_iff.mp (by simpa only [neg_sub, m5_redPt] using m2_parB_222 T h))
  have hGb : (⟨T.constellationPoint ⟨.green, 2, 2⟩,
      T.constellationPoint ⟨.green, 1, 0⟩ -
        T.constellationPoint ⟨.green, 2, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 2, 2⟩) :=
    Line.mem_base _
  have hGc : (⟨T.constellationPoint ⟨.green, 2, 2⟩,
      T.constellationPoint ⟨.green, 1, 0⟩ -
        T.constellationPoint ⟨.green, 2, 2⟩,
      hdirne⟩ : Line E).mem (T.constellationPoint ⟨.green, 1, 0⟩) := by
    refine ⟨1, ?_⟩
    rw [one_smul, add_comm, sub_add_cancel]
  have hiff := m4_mem_iff_of_two_mem (hXY := m3_cp_ne T h (by decide :
      (⟨.green, 2, 2⟩ : ConstellationIndex) ≠ ⟨.green, 1, 0⟩))
    (m3LC0_green_2_2 T h) (m3LC0_green_1_0 T h) hGb hGc
  exact (hiff _).mpr hG


theorem m3LC0_side (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    Parallel (m3pSide T (1 : TrisectorLabel)) (m3LC0 T h).direction := by
  have hpar := m3p_red_par23 T (0 : TrisectorLabel)
  have hpar' : Parallel (m3pSide T (1 : TrisectorLabel))
      (T.m5_redPt ⟨2, 1⟩ - T.m5_redPt ⟨1, 2⟩) := by
    simpa only [m5_redPt, show ((0 : TrisectorLabel) + 0) = 0 from by decide, show ((0 : TrisectorLabel) + 1) = 1 from by decide, show ((0 : TrisectorLabel) + 2) = 2 from by decide] using hpar
  have hv : T.m5_redPt ⟨2, 1⟩ - T.m5_redPt ⟨1, 2⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨2, 1⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨1, 2⟩))
  have hqv : T.m5_redPt ⟨1, 2⟩ - T.m5_redPt ⟨2, 1⟩ ≠ 0 :=
    sub_ne_zero.mpr (m3_red_ne T h (by decide :
      (⟨1, 2⟩ : TrisectorLabel × TrisectorLabel) ≠ ⟨2, 1⟩))
  have hside : m3pSide T (1 : TrisectorLabel) ≠ 0 := m3_side_ne_of_par T _ hv hpar'
  unfold m3LC0 m3lineThrough
  exact (m3_par_par_iff hside hv hpar').mpr (by
    simpa only [neg_sub] using m3_par_neg_left_iff.mpr (m3sgnDir_parallel hqv))

theorem m3LC0_dir (T : OrientedTriangle E o) (h : Injective T.constellationPoint) :
    T.parallelToMorleySide (m3LC0 T h).direction :=
  m3p_side_ptM T (1 : TrisectorLabel) (m3LC0_side T h)


end OrientedTriangle
end XamboMorley
